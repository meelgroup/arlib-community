/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPrimitives
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofTruncation
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Group.LIntegral

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-! # Restricted-Gaussian laws used by the implemented walk

This file connects the real-valued partition functions used in the ratio
proof to actual probability measures. It is the measure-theoretic entry point
for warm starts and mixing of `truncatedMetropolisBallStep`.
-/

theorem uniformUnitIntervalMeasure_eq_restrict :
    uniformUnitIntervalMeasure = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  unfold uniformUnitIntervalMeasure
  let finite : FiniteMeasure ℝ := uniformUnitIntervalFiniteMeasure
  have hmass : finite.mass = 1 := by
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass]
    change volume.restrict (Set.Icc (0 : ℝ) 1) Set.univ = (1 : ENNReal)
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  have hfinite : finite ≠ 0 := finite.mass_nonzero_iff.mp (by simp [hmass])
  change (finite.normalize : Measure ℝ) = _
  rw [finite.toMeasure_normalize_eq_of_nonzero hfinite, hmass]
  simp
  change (uniformUnitIntervalFiniteMeasure : Measure ℝ) = _
  rfl

theorem uniformUnitIntervalMeasure_Iic {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    uniformUnitIntervalMeasure (Set.Iic a) = ENNReal.ofReal a := by
  rw [uniformUnitIntervalMeasure_eq_restrict,
    Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 a := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hxa, hx0, _hx1⟩
      exact ⟨hx0, hxa⟩
    · rintro ⟨hx0, hxa⟩
      exact ⟨hxa, hx0, hxa.trans ha1⟩
  rw [hset, Real.volume_Icc]
  simp

theorem uniformUnitIntervalMeasure_Ioi {a : ℝ} (ha0 : 0 ≤ a) (_ha1 : a ≤ 1) :
    uniformUnitIntervalMeasure (Set.Ioi a) = ENNReal.ofReal (1 - a) := by
  rw [uniformUnitIntervalMeasure_eq_restrict,
    Measure.restrict_apply measurableSet_Ioi]
  have hset : Set.Ioi a ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc a 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hax, _hx0, hx1⟩
      exact ⟨hax, hx1⟩
    · rintro ⟨hax, hx1⟩
      exact ⟨hax, ha0.trans hax.le, hx1⟩
  rw [hset, Real.volume_Ioc]

theorem uniformUnitInterval_map_threshold {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {E : Type*} [MeasurableSpace E] (accepted rejected : E) :
    uniformUnitIntervalMeasure.map
        (fun coin => if coin ≤ a then accepted else rejected) =
      ENNReal.ofReal a • Measure.dirac accepted +
        ENNReal.ofReal (1 - a) • Measure.dirac rejected := by
  have hmap : Measurable fun coin : ℝ =>
      if coin ≤ a then accepted else rejected := by
    exact Measurable.ite measurableSet_Iic measurable_const measurable_const
  ext S hS
  rw [Measure.map_apply hmap hS, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply]
  by_cases haS : accepted ∈ S <;> by_cases hrS : rejected ∈ S
  · have hpre : (fun coin : ℝ =>
        if coin ≤ a then accepted else rejected) ⁻¹' S = Set.univ := by
      ext coin
      by_cases hcoin : coin ≤ a
      · simp [hcoin, haS]
      · simp [hcoin, hrS]
    rw [hpre]
    simp [Measure.dirac_apply' _ hS, haS, hrS]
    rw [← ENNReal.ofReal_add ha0 (sub_nonneg.mpr ha1)]
    norm_num
  · have hpre : (fun coin : ℝ =>
        if coin ≤ a then accepted else rejected) ⁻¹' S = Set.Iic a := by
      ext coin
      by_cases hcoin : coin ≤ a <;> simp [hcoin, haS, hrS]
    rw [hpre, uniformUnitIntervalMeasure_Iic ha0 ha1]
    simp [Measure.dirac_apply' _ hS, haS, hrS]
  · have hpre : (fun coin : ℝ =>
        if coin ≤ a then accepted else rejected) ⁻¹' S = Set.Ioi a := by
      ext coin
      by_cases hcoin : coin ≤ a
      · simp [hcoin, haS]
      · simp [hcoin, hrS, lt_of_not_ge hcoin]
    rw [hpre, uniformUnitIntervalMeasure_Ioi ha0 ha1]
    simp [Measure.dirac_apply' _ hS, haS, hrS]
  · have hpre : (fun coin : ℝ =>
        if coin ≤ a then accepted else rejected) ⁻¹' S = ∅ := by
      ext coin
      by_cases hcoin : coin ≤ a <;> simp [hcoin, haS, hrS]
    rw [hpre]
    simp [Measure.dirac_apply' _ hS, haS, hrS]

theorem volume_restrict_centeredClosedBall_map_neg (n : ℕ) (radius : ℝ) :
    (volume.restrict (Metric.closedBall (0 : AmbientSpace n) radius)).map
        (fun x => -x) =
      volume.restrict (Metric.closedBall (0 : AmbientSpace n) radius) := by
  have hpre : (fun x : AmbientSpace n => -x) ⁻¹'
      Metric.closedBall (0 : AmbientSpace n) radius =
        Metric.closedBall 0 radius := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  have hrestrict := Measure.restrict_map
    (μ := (volume : Measure (AmbientSpace n)))
    (f := fun x : AmbientSpace n => -x)
    (s := Metric.closedBall (0 : AmbientSpace n) radius)
    measurable_neg Metric.isClosed_closedBall.measurableSet
  rw [hpre] at hrestrict
  calc
    (volume.restrict (Metric.closedBall (0 : AmbientSpace n) radius)).map
        (fun x => -x) =
        (volume.map fun x : AmbientSpace n => -x).restrict
          (Metric.closedBall 0 radius) := hrestrict.symm
    _ = volume.restrict (Metric.closedBall 0 radius) := by
      rw [Measure.map_neg_eq_self]

theorem centeredClosedBallMeasure_map_neg (n : ℕ) {radius : ℝ}
    (hradius : 0 < radius) :
    (centeredClosedBallMeasure n radius).map (fun x => -x) =
      centeredClosedBallMeasure n radius := by
  let finite : FiniteMeasure (AmbientSpace n) :=
    centeredClosedBallFiniteMeasure n radius
  have hfinite : finite ≠ 0 := by
    intro hzero
    have huniv : (finite : Measure (AmbientSpace n)) Set.univ = 0 := by
      rw [hzero]
      rfl
    change volume.restrict (Metric.closedBall (0 : AmbientSpace n) radius)
      Set.univ = 0 at huniv
    rw [Measure.restrict_apply_univ] at huniv
    exact (Metric.measure_closedBall_pos volume (0 : AmbientSpace n) hradius).ne' huniv
  unfold centeredClosedBallMeasure
  change Measure.map (fun x : AmbientSpace n => -x)
      (finite.normalize : Measure (AmbientSpace n)) =
    (finite.normalize : Measure (AmbientSpace n))
  rw [finite.toMeasure_normalize_eq_of_nonzero hfinite, Measure.map_smul]
  exact congrArg (fun μ : Measure (AmbientSpace n) => finite.mass⁻¹ • μ)
    (volume_restrict_centeredClosedBall_map_neg n radius)

/-- Lebesgue starting points together with a symmetric centered-ball offset
give the same joint flow after exchanging the two endpoints. -/
theorem centeredClosedBall_flow_swap (n : ℕ) {radius : ℝ}
    (hradius : 0 < radius) (F : AmbientSpace n → AmbientSpace n → ENNReal)
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ x, ∫⁻ z, F x (x + z) ∂(centeredClosedBallMeasure n radius) ∂volume) =
      ∫⁻ y, ∫⁻ z, F (y + z) y ∂(centeredClosedBallMeasure n radius) ∂volume := by
  let ν : Measure (AmbientSpace n) := centeredClosedBallMeasure n radius
  have hleft : Measurable fun p : AmbientSpace n × AmbientSpace n =>
      F p.1 (p.1 + p.2) :=
    hF.comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  have hright : Measurable fun p : AmbientSpace n × AmbientSpace n =>
      F (p.1 + p.2) p.1 :=
    hF.comp ((measurable_fst.add measurable_snd).prodMk measurable_fst)
  have hright' : Measurable fun p : AmbientSpace n × AmbientSpace n =>
      F (p.2 + p.1) p.2 :=
    hF.comp ((measurable_snd.add measurable_fst).prodMk measurable_snd)
  calc
    (∫⁻ x, ∫⁻ z, F x (x + z) ∂ν ∂volume) =
        ∫⁻ z, ∫⁻ x, F x (x + z) ∂volume ∂ν :=
      lintegral_lintegral_swap hleft.aemeasurable
    _ = ∫⁻ z, ∫⁻ y, F (y - z) y ∂volume ∂ν := by
      apply lintegral_congr
      intro z
      have htranslate := lintegral_add_right_eq_self
        (μ := (volume : Measure (AmbientSpace n)))
        (fun y => F (y - z) y) z
      simpa [sub_eq_add_neg, add_assoc] using htranslate
    _ = ∫⁻ z, ∫⁻ y, F (y + z) y ∂volume ∂ν := by
      let H : AmbientSpace n → ENNReal := fun z =>
        ∫⁻ y, F (y + z) y ∂volume
      have hH : Measurable H := by
        exact Measurable.lintegral_prod_right hright'
      change (∫⁻ z, H (-z) ∂ν) = ∫⁻ z, H z ∂ν
      rw [← lintegral_map hH measurable_neg]
      exact congrArg (fun μ : Measure (AmbientSpace n) => ∫⁻ z, H z ∂μ)
        (centeredClosedBallMeasure_map_neg n hradius)
    _ = ∫⁻ y, ∫⁻ z, F (y + z) y ∂ν ∂volume :=
      (lintegral_lintegral_swap hright.aemeasurable).symm

/-- The unnormalized Gaussian measure on the fixed truncated body. -/
noncomputable def truncatedGaussianMeasure (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) : Measure (AmbientSpace q.n) :=
  (volume.restrict (truncatedBody q I)).withDensity fun x =>
    ENNReal.ofReal (gaussianDensity sigma2 x)

/-- The same unnormalized density, extended by zero off the truncated body. -/
noncomputable def truncatedGaussianENNRealDensity (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) (x : AmbientSpace q.n) : ENNReal :=
  (truncatedBody q I).indicator
    (fun y => ENNReal.ofReal (gaussianDensity sigma2 y)) x

theorem measurable_truncatedGaussianENNRealDensity (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable (truncatedGaussianENNRealDensity q I sigma2) := by
  unfold truncatedGaussianENNRealDensity
  apply Measurable.indicator
  · apply ENNReal.measurable_ofReal.comp
    unfold gaussianDensity
    fun_prop
  · exact truncatedBody_measurable q I

theorem truncatedGaussianMeasure_eq_withDensity (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) :
    truncatedGaussianMeasure q I sigma2 =
      volume.withDensity (truncatedGaussianENNRealDensity q I sigma2) := by
  unfold truncatedGaussianMeasure truncatedGaussianENNRealDensity
  exact (withDensity_indicator (truncatedBody_measurable q I) _).symm

/-- The estimate semantics of one implemented truncated Metropolis step,
packaged as a Markov kernel. -/
noncomputable def truncatedMetropolisKernel (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) (sigma2 : ℝ) :
    ProbabilityTheory.Kernel (AmbientSpace q.n) (AmbientSpace q.n) where
  toFun := truncatedMetropolisBallStepEstimateLaw q oracle.query sigma2
  measurable' :=
    measurable_truncatedMetropolisBallStepEstimateLaw q I oracle sigma2

instance truncatedMetropolisKernel_isMarkov (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) (sigma2 : ℝ) :
    ProbabilityTheory.IsMarkovKernel
      (truncatedMetropolisKernel q I oracle sigma2) := by
  constructor
  intro current
  change IsProbabilityMeasure
    (truncatedMetropolisBallStepEstimateLaw q oracle.query sigma2 current)
  rw [← runEstimate_truncatedMetropolisBallStep q I oracle sigma2 current]
  exact MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
    (truncatedMetropolisBallStep_stronglyMeasurable
      q I oracle sigma2 current).estimateMeasurable

theorem runEstimate_truncatedMetropolisBallWalk_eq_kernel_pow
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) : ∀ steps current,
    (truncatedMetropolisBallWalk q sigma2 steps current).runEstimate oracle.query =
      (truncatedMetropolisKernel q I oracle sigma2 ^ steps) current := by
  intro steps
  induction steps with
  | zero =>
      intro current
      rw [truncatedMetropolisBallWalk, MembershipOracleProgram.runEstimate]
      change Measure.dirac current = Measure.dirac current
      rfl
  | succ steps ih =>
      intro current
      simp only [truncatedMetropolisBallWalk]
      have hwalk := truncatedMetropolisBallWalk_measurable_and_strong
        q I oracle sigma2 steps
      rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
        (truncatedMetropolisBallStep_stronglyMeasurable
          q I oracle sigma2 current) hwalk.2 hwalk.1]
      rw [runEstimate_truncatedMetropolisBallStep q I oracle sigma2 current]
      simp_rw [ih]
      rw [pow_succ]
      rfl

private theorem mul_lazyMinRatio_comm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * (min 1 (b / a) / 2) = b * (min 1 (a / b) / 2) := by
  rcases le_total a b with hab | hba
  · have hbaRatio : 1 ≤ b / a := (le_div_iff₀ ha).2 (by simpa using hab)
    have habRatio : a / b ≤ 1 := (div_le_one hb).2 hab
    rw [min_eq_left hbaRatio, min_eq_right habRatio]
    field_simp
  · have habRatio : 1 ≤ a / b := (le_div_iff₀ hb).2 (by simpa using hba)
    have hbaRatio : b / a ≤ 1 := (div_le_one ha).2 hba
    rw [min_eq_right hbaRatio, min_eq_left habRatio]
    field_simp

/-- Pointwise detailed balance for the lazy Gaussian Metropolis filter.  The
remaining stationarity proof only has to combine this identity with symmetry
of the translated-ball proposal and the reject-to-self mass. -/
theorem gaussianDensity_mul_lazyAcceptance_comm {n : ℕ} (sigma2 : ℝ)
    (x y : AmbientSpace n) :
    gaussianDensity sigma2 x * lazyGaussianMetropolisAcceptance sigma2 x y =
      gaussianDensity sigma2 y * lazyGaussianMetropolisAcceptance sigma2 y x := by
  rw [gaussianDensity_eq, gaussianDensity_eq]
  unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
  exact mul_lazyMinRatio_comm (Real.exp_pos _) (Real.exp_pos _)

theorem oracle_and_radius_iff_mem_truncatedBody (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (x : AmbientSpace q.n) :
    oracle.query x = true ∧ ‖x‖ ≤ Real.sqrt (terminalVariance q) ↔
      x ∈ truncatedBody q I := by
  rw [oracle.correct]
  simp only [truncatedBody, Set.mem_inter_iff, Metric.mem_closedBall,
    dist_zero_right]

theorem lazyGaussianMetropolisAcceptance_nonneg {n : ℕ} (sigma2 : ℝ)
    (x y : AmbientSpace n) :
    0 ≤ lazyGaussianMetropolisAcceptance sigma2 x y := by
  unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
  have hratio : 0 ≤
      Real.exp (-‖y‖ ^ 2 / (2 * sigma2)) /
        Real.exp (-‖x‖ ^ 2 / (2 * sigma2)) := by positivity
  positivity

theorem lazyGaussianMetropolisAcceptance_le_one {n : ℕ} (sigma2 : ℝ)
    (x y : AmbientSpace n) :
    lazyGaussianMetropolisAcceptance sigma2 x y ≤ 1 := by
  unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
  have hmin : min 1
      (Real.exp (-‖y‖ ^ 2 / (2 * sigma2)) /
        Real.exp (-‖x‖ ^ 2 / (2 * sigma2))) ≤ 1 := min_le_left _ _
  linarith

theorem truncatedMetropolisProposalEstimateLaw_of_eligible
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n)
    (heligible : oracle.query proposal = true ∧
      ‖proposal‖ ≤ Real.sqrt (terminalVariance q)) :
    truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 current proposal =
      ENNReal.ofReal (lazyGaussianMetropolisAcceptance sigma2 current proposal) •
          Measure.dirac proposal +
        ENNReal.ofReal
            (1 - lazyGaussianMetropolisAcceptance sigma2 current proposal) •
          Measure.dirac current := by
  unfold truncatedMetropolisProposalEstimateLaw
  simp only [heligible.1, heligible.2, true_and]
  exact uniformUnitInterval_map_threshold
    (lazyGaussianMetropolisAcceptance_nonneg sigma2 current proposal)
    (lazyGaussianMetropolisAcceptance_le_one sigma2 current proposal)
    proposal current

theorem truncatedMetropolisProposalEstimateLaw_of_ineligible
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n)
    (hineligible : ¬ (oracle.query proposal = true ∧
      ‖proposal‖ ≤ Real.sqrt (terminalVariance q))) :
    truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 current proposal = Measure.dirac current := by
  unfold truncatedMetropolisProposalEstimateLaw
  have hfun : (fun coin : ℝ =>
      if oracle.query proposal = true ∧
          ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
          coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal
        then proposal else current) = fun _ => current := by
    funext coin
    have hfull : ¬ (oracle.query proposal = true ∧
        ‖proposal‖ ≤ Real.sqrt (terminalVariance q) ∧
        coin ≤ lazyGaussianMetropolisAcceptance sigma2 current proposal) := by
      intro h
      exact hineligible ⟨h.1, h.2.1⟩
    simp [hfull]
  rw [hfun]
  rw [Measure.map_const]
  simp

/-- Acceptance probability after incorporating membership in the fixed
truncated body. -/
noncomputable def truncatedMetropolisAcceptance (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) : ℝ :=
  (truncatedBody q I).indicator
    (fun y => lazyGaussianMetropolisAcceptance sigma2 current y) proposal

theorem truncatedMetropolisAcceptance_nonneg (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    0 ≤ truncatedMetropolisAcceptance q I sigma2 current proposal := by
  unfold truncatedMetropolisAcceptance
  by_cases h : proposal ∈ truncatedBody q I
  · rw [Set.indicator_of_mem h]
    exact lazyGaussianMetropolisAcceptance_nonneg sigma2 current proposal
  · rw [Set.indicator_of_notMem h]

theorem truncatedMetropolisAcceptance_le_one (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ)
    (current proposal : AmbientSpace q.n) :
    truncatedMetropolisAcceptance q I sigma2 current proposal ≤ 1 := by
  unfold truncatedMetropolisAcceptance
  by_cases h : proposal ∈ truncatedBody q I
  · rw [Set.indicator_of_mem h]
    exact lazyGaussianMetropolisAcceptance_le_one sigma2 current proposal
  · rw [Set.indicator_of_notMem h]
    norm_num

theorem measurable_truncatedMetropolisAcceptance (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) :
    Measurable fun p : AmbientSpace q.n × AmbientSpace q.n =>
      truncatedMetropolisAcceptance q I sigma2 p.1 p.2 := by
  unfold truncatedMetropolisAcceptance
  apply Measurable.indicator
  · unfold lazyGaussianMetropolisAcceptance gaussianMetropolisAcceptance
    fun_prop
  · exact (truncatedBody_measurable q I).preimage measurable_snd

/-- Detailed balance after both the target support and the proposal-membership
test have been folded into their extended-by-zero densities. -/
theorem truncatedGaussianDensity_acceptance_comm
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (x y : AmbientSpace q.n) :
    truncatedGaussianENNRealDensity q I sigma2 x *
        ENNReal.ofReal (truncatedMetropolisAcceptance q I sigma2 x y) =
      truncatedGaussianENNRealDensity q I sigma2 y *
        ENNReal.ofReal (truncatedMetropolisAcceptance q I sigma2 y x) := by
  by_cases hx : x ∈ truncatedBody q I <;>
    by_cases hy : y ∈ truncatedBody q I
  · simp only [truncatedGaussianENNRealDensity,
      Set.indicator_of_mem hx, Set.indicator_of_mem hy,
      truncatedMetropolisAcceptance]
    rw [← ENNReal.ofReal_mul (by
      unfold gaussianDensity
      positivity), ← ENNReal.ofReal_mul (by
      unfold gaussianDensity
      positivity)]
    exact congrArg ENNReal.ofReal
      (gaussianDensity_mul_lazyAcceptance_comm sigma2 x y)
  · simp [truncatedGaussianENNRealDensity, truncatedMetropolisAcceptance,
      hx, hy]
  · simp [truncatedGaussianENNRealDensity, truncatedMetropolisAcceptance,
      hx, hy]
  · simp [truncatedGaussianENNRealDensity, truncatedMetropolisAcceptance,
      hx, hy]

/-- Exact accepted-move plus reject-to-self formula for the program's inner
coin-filtered proposal law. -/
theorem truncatedMetropolisProposalEstimateLaw_eq_mixture
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current proposal : AmbientSpace q.n) :
    truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 current proposal =
      ENNReal.ofReal
          (truncatedMetropolisAcceptance q I sigma2 current proposal) •
        Measure.dirac proposal +
      ENNReal.ofReal
          (1 - truncatedMetropolisAcceptance q I sigma2 current proposal) •
        Measure.dirac current := by
  by_cases hproposal : proposal ∈ truncatedBody q I
  · have heligible : oracle.query proposal = true ∧
        ‖proposal‖ ≤ Real.sqrt (terminalVariance q) :=
      (oracle_and_radius_iff_mem_truncatedBody q I oracle proposal).2 hproposal
    rw [truncatedMetropolisProposalEstimateLaw_of_eligible
      q I oracle sigma2 current proposal heligible]
    simp [truncatedMetropolisAcceptance, Set.indicator_of_mem hproposal]
  · have hineligible : ¬ (oracle.query proposal = true ∧
        ‖proposal‖ ≤ Real.sqrt (terminalVariance q)) := by
      rwa [oracle_and_radius_iff_mem_truncatedBody q I oracle proposal]
    rw [truncatedMetropolisProposalEstimateLaw_of_ineligible
      q I oracle sigma2 current proposal hineligible]
    simp [truncatedMetropolisAcceptance, Set.indicator_of_notMem hproposal]

theorem figureOneProposalRadius_pos (q : VolumeParams) {sigma2 : ℝ}
    (hsigma2 : 0 < sigma2) : 0 < figureOneProposalRadius q sigma2 := by
  unfold figureOneProposalRadius protectedLog
  have hn : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) q.dim_ok)
  have hlog : 0 < max 1 (Real.log ((q.n : ℝ) / q.eps)) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsqrt : 0 < Real.sqrt sigma2 := Real.sqrt_pos.2 hsigma2
  exact div_pos (lt_min hsqrt zero_lt_one) (by positivity)

theorem truncatedMetropolisKernel_apply
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) (current : AmbientSpace q.n)
    {B : Set (AmbientSpace q.n)} (hB : MeasurableSet B) :
    truncatedMetropolisKernel q I oracle sigma2 current B =
      ∫⁻ z,
        ENNReal.ofReal
            (truncatedMetropolisAcceptance q I sigma2 current (current + z)) *
              B.indicator 1 (current + z) +
          ENNReal.ofReal
            (1 - truncatedMetropolisAcceptance q I sigma2 current (current + z)) *
              B.indicator 1 current
        ∂(centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2)) := by
  change (truncatedMetropolisBallStepEstimateLaw
    q oracle.query sigma2 current) B = _
  unfold truncatedMetropolisBallStepEstimateLaw
  have hproposal : Measurable fun z : AmbientSpace q.n =>
      truncatedMetropolisProposalEstimateLaw oracle.query
        (terminalVariance q) sigma2 current (current + z) :=
    (measurable_truncatedMetropolisProposalEstimateLaw q I oracle sigma2).comp
      (measurable_const.prodMk (measurable_const.add measurable_id))
  rw [Measure.bind_apply hB hproposal.aemeasurable]
  apply lintegral_congr
  intro z
  rw [truncatedMetropolisProposalEstimateLaw_eq_mixture
    q I oracle sigma2 current (current + z), Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hB, Measure.dirac_apply' _ hB]
  simp only [smul_eq_mul]

/-- Symmetry of the accepted-move flow.  This is the off-diagonal part of
reversibility; the reject-to-self part is symmetric separately. -/
theorem truncatedMetropolisAcceptedFlow_comm
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (hsigma2 : 0 < sigma2) {A B : Set (AmbientSpace q.n)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ x, ∫⁻ z,
        A.indicator 1 x * truncatedGaussianENNRealDensity q I sigma2 x *
          ENNReal.ofReal
            (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
          B.indicator 1 (x + z)
        ∂(centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2))
      ∂volume) =
    ∫⁻ y, ∫⁻ z,
        B.indicator 1 y * truncatedGaussianENNRealDensity q I sigma2 y *
          ENNReal.ofReal
            (truncatedMetropolisAcceptance q I sigma2 y (y + z)) *
          A.indicator 1 (y + z)
        ∂(centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2))
      ∂volume := by
  let F : AmbientSpace q.n → AmbientSpace q.n → ENNReal := fun x y =>
    A.indicator 1 x * truncatedGaussianENNRealDensity q I sigma2 x *
      ENNReal.ofReal (truncatedMetropolisAcceptance q I sigma2 x y) *
      B.indicator 1 y
  have hAind : Measurable (A.indicator (1 : AmbientSpace q.n → ENNReal)) :=
    measurable_const.indicator hA
  have hBind : Measurable (B.indicator (1 : AmbientSpace q.n → ENNReal)) :=
    measurable_const.indicator hB
  have hacc : Measurable fun p : AmbientSpace q.n × AmbientSpace q.n =>
      ENNReal.ofReal (truncatedMetropolisAcceptance q I sigma2 p.1 p.2) :=
    ENNReal.measurable_ofReal.comp
      (measurable_truncatedMetropolisAcceptance q I sigma2)
  have hF : Measurable (Function.uncurry F) := by
    exact (((hAind.comp measurable_fst).mul
      ((measurable_truncatedGaussianENNRealDensity q I sigma2).comp
        measurable_fst)).mul hacc).mul (hBind.comp measurable_snd)
  calc
    (∫⁻ x, ∫⁻ z,
        A.indicator 1 x * truncatedGaussianENNRealDensity q I sigma2 x *
          ENNReal.ofReal
            (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
          B.indicator 1 (x + z)
        ∂(centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2))
      ∂volume) =
      ∫⁻ y, ∫⁻ z, F (y + z) y
        ∂(centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2))
        ∂volume :=
      centeredClosedBall_flow_swap q.n
        (figureOneProposalRadius_pos q hsigma2) F hF
    _ = ∫⁻ y, ∫⁻ z,
        B.indicator 1 y * truncatedGaussianENNRealDensity q I sigma2 y *
          ENNReal.ofReal
            (truncatedMetropolisAcceptance q I sigma2 y (y + z)) *
          A.indicator 1 (y + z)
        ∂(centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2))
      ∂volume := by
      apply lintegral_congr
      intro y
      apply lintegral_congr
      intro z
      dsimp [F]
      have hbalance := truncatedGaussianDensity_acceptance_comm
        q I sigma2 (y + z) y
      calc
        A.indicator 1 (y + z) *
              truncatedGaussianENNRealDensity q I sigma2 (y + z) *
              ENNReal.ofReal
                (truncatedMetropolisAcceptance q I sigma2 (y + z) y) *
              B.indicator 1 y =
            A.indicator 1 (y + z) *
              (truncatedGaussianENNRealDensity q I sigma2 (y + z) *
                ENNReal.ofReal
                  (truncatedMetropolisAcceptance q I sigma2 (y + z) y)) *
              B.indicator 1 y := by ac_rfl
        _ = A.indicator 1 (y + z) *
              (truncatedGaussianENNRealDensity q I sigma2 y *
                ENNReal.ofReal
                  (truncatedMetropolisAcceptance q I sigma2 y (y + z))) *
              B.indicator 1 y := by rw [hbalance]
        _ = B.indicator 1 y * truncatedGaussianENNRealDensity q I sigma2 y *
              ENNReal.ofReal
                (truncatedMetropolisAcceptance q I sigma2 y (y + z)) *
              A.indicator 1 (y + z) := by ac_rfl

noncomputable def truncatedMetropolisAcceptedFlow
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (A B : Set (AmbientSpace q.n)) : ENNReal :=
  ∫⁻ x, ∫⁻ z,
    A.indicator 1 x * truncatedGaussianENNRealDensity q I sigma2 x *
      ENNReal.ofReal
        (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
      B.indicator 1 (x + z)
    ∂(centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2)) ∂volume

noncomputable def truncatedMetropolisRejectedFlow
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (A B : Set (AmbientSpace q.n)) : ENNReal :=
  ∫⁻ x, ∫⁻ z,
    A.indicator 1 x * truncatedGaussianENNRealDensity q I sigma2 x *
      ENNReal.ofReal
        (1 - truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
      B.indicator 1 x
    ∂(centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2)) ∂volume

theorem truncatedMetropolisAcceptedFlow_comm'
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (hsigma2 : 0 < sigma2) {A B : Set (AmbientSpace q.n)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    truncatedMetropolisAcceptedFlow q I sigma2 A B =
      truncatedMetropolisAcceptedFlow q I sigma2 B A := by
  exact truncatedMetropolisAcceptedFlow_comm q I sigma2 hsigma2 hA hB

theorem truncatedMetropolisRejectedFlow_comm
    (q : VolumeParams) (I : VolumeInput q.n) (sigma2 : ℝ)
    (A B : Set (AmbientSpace q.n)) :
    truncatedMetropolisRejectedFlow q I sigma2 A B =
      truncatedMetropolisRejectedFlow q I sigma2 B A := by
  unfold truncatedMetropolisRejectedFlow
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro z
  ac_rfl

/-- Expanding the executable kernel against the unnormalized target measure
splits its flow into the accepted-move and reject-to-self terms above. -/
theorem truncatedMetropolis_raw_flow_eq_add
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (sigma2 : ℝ) {A B : Set (AmbientSpace q.n)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ x in A, truncatedMetropolisKernel q I oracle sigma2 x B
        ∂(truncatedGaussianMeasure q I sigma2)) =
      truncatedMetropolisAcceptedFlow q I sigma2 A B +
        truncatedMetropolisRejectedFlow q I sigma2 A B := by
  let d := truncatedGaussianENNRealDensity q I sigma2
  let ν := centeredClosedBallMeasure q.n (figureOneProposalRadius q sigma2)
  have hd : Measurable d :=
    measurable_truncatedGaussianENNRealDensity q I sigma2
  have hAind : Measurable (A.indicator (1 : AmbientSpace q.n → ENNReal)) :=
    measurable_const.indicator hA
  have hBind : Measurable (B.indicator (1 : AmbientSpace q.n → ENNReal)) :=
    measurable_const.indicator hB
  have haccPair : Measurable fun p : AmbientSpace q.n × AmbientSpace q.n =>
      ENNReal.ofReal
        (truncatedMetropolisAcceptance q I sigma2 p.1 (p.1 + p.2)) := by
    apply ENNReal.measurable_ofReal.comp
    exact (measurable_truncatedMetropolisAcceptance q I sigma2).comp
      (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  have hrejPair : Measurable fun p : AmbientSpace q.n × AmbientSpace q.n =>
      ENNReal.ofReal
        (1 - truncatedMetropolisAcceptance q I sigma2 p.1 (p.1 + p.2)) := by
    apply ENNReal.measurable_ofReal.comp
    exact measurable_const.sub <|
      (measurable_truncatedMetropolisAcceptance q I sigma2).comp
        (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  have hacceptedPair : Measurable fun p : AmbientSpace q.n × AmbientSpace q.n =>
      A.indicator 1 p.1 * d p.1 *
        ENNReal.ofReal
          (truncatedMetropolisAcceptance q I sigma2 p.1 (p.1 + p.2)) *
        B.indicator 1 (p.1 + p.2) := by
    exact (((hAind.comp measurable_fst).mul (hd.comp measurable_fst)).mul
      haccPair).mul (hBind.comp (measurable_fst.add measurable_snd))
  have hrejectedPair : Measurable fun p : AmbientSpace q.n × AmbientSpace q.n =>
      A.indicator 1 p.1 * d p.1 *
        ENNReal.ofReal
          (1 - truncatedMetropolisAcceptance q I sigma2 p.1 (p.1 + p.2)) *
        B.indicator 1 p.1 := by
    exact (((hAind.comp measurable_fst).mul (hd.comp measurable_fst)).mul
      hrejPair).mul (hBind.comp measurable_fst)
  rw [truncatedGaussianMeasure_eq_withDensity]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul volume hd
    (ProbabilityTheory.Kernel.measurable_coe
      (truncatedMetropolisKernel q I oracle sigma2) hB) hA]
  rw [← lintegral_indicator hA]
  have hpointwise : ∀ x : AmbientSpace q.n,
      A.indicator
          (fun x => d x * truncatedMetropolisKernel q I oracle sigma2 x B) x =
        (∫⁻ z,
          A.indicator 1 x * d x *
            ENNReal.ofReal
              (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
            B.indicator 1 (x + z) ∂ν) +
        ∫⁻ z,
          A.indicator 1 x * d x *
            ENNReal.ofReal
              (1 - truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
            B.indicator 1 x ∂ν := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp only [Pi.one_apply, one_mul]
      rw [truncatedMetropolisKernel_apply q I oracle sigma2 x hB]
      have haccZ : Measurable fun z : AmbientSpace q.n =>
          ENNReal.ofReal
              (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
            B.indicator 1 (x + z) := by
        exact (haccPair.comp (measurable_const.prodMk measurable_id)).mul
          (hBind.comp (measurable_const.add measurable_id))
      have hrejZ : Measurable fun z : AmbientSpace q.n =>
          ENNReal.ofReal
              (1 - truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
            B.indicator 1 x := by
        exact (hrejPair.comp (measurable_const.prodMk measurable_id)).mul
          measurable_const
      have haccFull : Measurable fun z : AmbientSpace q.n =>
          d x * ENNReal.ofReal
              (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
            B.indicator 1 (x + z) := by
        exact (measurable_const.mul
          (haccPair.comp (measurable_const.prodMk measurable_id))).mul
            (hBind.comp (measurable_const.add measurable_id))
      calc
        d x * ∫⁻ z,
            ENNReal.ofReal
                (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
                B.indicator 1 (x + z) +
              ENNReal.ofReal
                (1 - truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
                B.indicator 1 x ∂ν =
            ∫⁻ z, d x *
              (ENNReal.ofReal
                  (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
                  B.indicator 1 (x + z) +
                ENNReal.ofReal
                  (1 - truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
                  B.indicator 1 x) ∂ν :=
          (lintegral_const_mul (μ := ν) (d x) (haccZ.add hrejZ)).symm
        _ = ∫⁻ z,
              d x * ENNReal.ofReal
                  (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
                  B.indicator 1 (x + z) +
              d x * ENNReal.ofReal
                  (1 - truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
                  B.indicator 1 x ∂ν := by
          apply lintegral_congr
          intro z
          ring
        _ = (∫⁻ z,
              d x * ENNReal.ofReal
                  (truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
                  B.indicator 1 (x + z) ∂ν) +
            ∫⁻ z,
              d x * ENNReal.ofReal
                  (1 - truncatedMetropolisAcceptance q I sigma2 x (x + z)) *
                  B.indicator 1 x ∂ν := by
          exact lintegral_add_left (μ := ν) haccFull _
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  change (∫⁻ x, A.indicator
    (fun x => d x * truncatedMetropolisKernel q I oracle sigma2 x B) x ∂volume) = _
  rw [lintegral_congr hpointwise,
    lintegral_add_left (Measurable.lintegral_prod_right hacceptedPair)]
  unfold truncatedMetropolisAcceptedFlow truncatedMetropolisRejectedFlow
  rfl

theorem truncatedMetropolisKernel_isReversible_raw
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ProbabilityTheory.Kernel.IsReversible
      (truncatedMetropolisKernel q I oracle sigma2)
      (truncatedGaussianMeasure q I sigma2) := by
  intro A B hA hB
  rw [truncatedMetropolis_raw_flow_eq_add q I oracle sigma2 hA hB,
    truncatedMetropolis_raw_flow_eq_add q I oracle sigma2 hB hA,
    truncatedMetropolisAcceptedFlow_comm' q I sigma2 hsigma2 hA hB,
    truncatedMetropolisRejectedFlow_comm q I sigma2 A B]

theorem truncatedGaussianMeasure_isFinite (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    IsFiniteMeasure (truncatedGaussianMeasure q I sigma2) := by
  unfold truncatedGaussianMeasure
  exact isFiniteMeasure_withDensity_ofReal
    (integrable_gaussianDensity (n := q.n) hsigma2 |>.integrableOn |>.hasFiniteIntegral)

theorem truncatedGaussianMeasure_apply_univ (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    truncatedGaussianMeasure q I sigma2 Set.univ =
      ENNReal.ofReal (gaussianIntegral (truncatedBody q I) sigma2) := by
  have hK := truncatedBody_measurable q I
  have hf := integrable_gaussianDensity (n := q.n) hsigma2
  unfold truncatedGaussianMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrableOn
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  congr 1
  simp [gaussianIntegral_eq_setIntegral hK]

theorem truncatedGaussianMeasure_ne_zero (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    truncatedGaussianMeasure q I sigma2 ≠ 0 := by
  intro hzero
  have huniv : truncatedGaussianMeasure q I sigma2 Set.univ = 0 := by
    rw [hzero]
    simp
  rw [truncatedGaussianMeasure_apply_univ q I hsigma2] at huniv
  exact (ENNReal.ofReal_pos.mpr <| by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2).ne' huniv

/-- The restricted Gaussian packaged as a finite measure. -/
noncomputable def truncatedGaussianFiniteMeasure (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) (hsigma2 : 0 < sigma2) :
    FiniteMeasure (AmbientSpace q.n) := by
  letI := truncatedGaussianMeasure_isFinite q I hsigma2
  exact ⟨truncatedGaussianMeasure q I sigma2, inferInstance⟩

/-- The normalized target law of every ball-walk phase. -/
noncomputable def truncatedGaussianProbability (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) (hsigma2 : 0 < sigma2) :
    ProbabilityMeasure (AmbientSpace q.n) :=
  (truncatedGaussianFiniteMeasure q I sigma2 hsigma2).normalize

theorem truncatedGaussianProbability_toMeasure (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) =
      (ENNReal.ofReal (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ •
        truncatedGaussianMeasure q I sigma2 := by
  let finite : FiniteMeasure (AmbientSpace q.n) :=
    truncatedGaussianFiniteMeasure q I sigma2 hsigma2
  have hfinite : finite ≠ 0 := by
    intro hzero
    have : truncatedGaussianMeasure q I sigma2 = 0 := by
      change (finite : Measure (AmbientSpace q.n)) = 0
      rw [hzero]
      rfl
    exact truncatedGaussianMeasure_ne_zero q I hsigma2 this
  change (finite.normalize : Measure (AmbientSpace q.n)) = _
  rw [finite.toMeasure_normalize_eq_of_nonzero hfinite]
  have hmass : (finite.mass : ENNReal) =
      ENNReal.ofReal (gaussianIntegral (truncatedBody q I) sigma2) := by
    rw [FiniteMeasure.ennreal_mass]
    exact truncatedGaussianMeasure_apply_univ q I hsigma2
  rw [← Measure.coe_nnreal_smul,
    ENNReal.coe_inv (finite.mass_nonzero_iff.mpr hfinite), hmass]
  rfl

theorem truncatedMetropolisKernel_isReversible
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ProbabilityTheory.Kernel.IsReversible
      (truncatedMetropolisKernel q I oracle sigma2)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) := by
  rw [truncatedGaussianProbability_toMeasure q I hsigma2]
  intro A B hA hB
  simp only [Measure.restrict_smul, lintegral_smul_measure]
  exact congrArg
    (fun value =>
      (ENNReal.ofReal (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ * value)
    (truncatedMetropolisKernel_isReversible_raw
      q I oracle hsigma2 hA hB)

theorem truncatedMetropolisKernel_invariant
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ProbabilityTheory.Kernel.Invariant
      (truncatedMetropolisKernel q I oracle sigma2)
      (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) :=
  (truncatedMetropolisKernel_isReversible q I oracle hsigma2).invariant

theorem truncatedGaussianProbability_apply (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {S : Set (AmbientSpace q.n)} (hS : MeasurableSet S) :
    (truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)) S =
      (ENNReal.ofReal (gaussianIntegral (truncatedBody q I) sigma2))⁻¹ *
        ∫⁻ x in S ∩ truncatedBody q I,
          ENNReal.ofReal (gaussianDensity sigma2 x) := by
  rw [truncatedGaussianProbability_toMeasure q I hsigma2,
    Measure.smul_apply, smul_eq_mul]
  unfold truncatedGaussianMeasure
  rw [withDensity_apply _ hS]
  rw [Measure.restrict_restrict hS]

/-- The normalized restricted Gaussian is almost surely supported on the
common truncated body. -/
theorem truncatedGaussianProbability_ae_mem (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ∀ᵐ x ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)), x ∈ truncatedBody q I := by
  change truncatedBody q I ∈
    ae (truncatedGaussianProbability q I sigma2 hsigma2 :
      Measure (AmbientSpace q.n))
  rw [mem_ae_iff]
  rw [truncatedGaussianProbability_apply q I hsigma2
    (truncatedBody_measurable q I).compl]
  simp

/-- Integration against the normalized restricted Gaussian is ordinary
Lebesgue integration against its density, divided by the partition function. -/
theorem integral_truncatedGaussianProbability (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (f : AmbientSpace q.n → ℝ) :
    (∫ x, f x ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n))) =
      (gaussianIntegral (truncatedBody q I) sigma2)⁻¹ *
        ∫ x in truncatedBody q I, f x * gaussianDensity sigma2 x := by
  rw [truncatedGaussianProbability_toMeasure q I hsigma2,
    integral_smul_measure]
  have hZ : 0 < gaussianIntegral (truncatedBody q I) sigma2 := by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I) hsigma2
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  unfold truncatedGaussianMeasure
  simp only [smul_eq_mul]
  change (gaussianIntegral (truncatedBody q I) sigma2)⁻¹ *
      (∫ x, f x ∂(volume.restrict (truncatedBody q I)).withDensity
        (ENNReal.ofReal ∘ gaussianDensity sigma2)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (ENNReal.measurable_ofReal.comp <| by
      unfold gaussianDensity
      fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  have hd : 0 ≤ gaussianDensity sigma2 x := by
    unfold gaussianDensity
    positivity
  simp [Function.comp_apply, ENNReal.toReal_ofReal hd, smul_eq_mul, mul_comm]

theorem gaussianRatioWeight_eq_sample (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 tau2 : ℝ) {x : AmbientSpace q.n}
    (hx : x ∈ truncatedBody q I) :
    gaussianRatioWeight sigma2 tau2 x =
      gaussianRatioSample (truncatedBody q I) sigma2 tau2 x := by
  simp [gaussianRatioWeight, gaussianRatioSample, unnormGaussian,
    Set.indicator_of_mem hx]

theorem uniformRatioWeight_eq_sample (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ) {x : AmbientSpace q.n}
    (hx : x ∈ truncatedBody q I) :
    uniformRatioWeight sigma2 x =
      uniformRatioSample (truncatedBody q I) sigma2 x := by
  simp [uniformRatioWeight, uniformRatioSample, Set.indicator_of_mem hx]

/-- The executable Gaussian ratio weight has the exact adjacent partition-
function ratio as its expectation under the stationary phase law. -/
theorem gaussianRatioWeight_mean_eq (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 tau2 : ℝ} (hsigma2 : 0 < sigma2) :
    (∫ x, gaussianRatioWeight sigma2 tau2 x
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))) =
      gaussianIntegral (truncatedBody q I) tau2 /
        gaussianIntegral (truncatedBody q I) sigma2 := by
  rw [integral_truncatedGaussianProbability q I hsigma2]
  have hweighted :
      (∫ x in truncatedBody q I,
          gaussianRatioWeight sigma2 tau2 x * gaussianDensity sigma2 x) =
        gaussianIntegral (truncatedBody q I) tau2 := by
    have hpaper := gaussianRatio_weightedIntegral q
      (truncatedVolumeInput q I) (tau2 := tau2) hsigma2
    simp only [truncatedVolumeInput_coe] at hpaper
    rw [← hpaper]
    apply setIntegral_congr_fun (truncatedBody_measurable q I)
    intro x hx
    change gaussianRatioWeight sigma2 tau2 x * gaussianDensity sigma2 x = _
    rw [gaussianRatioWeight_eq_sample q I sigma2 tau2 hx]
  rw [hweighted]
  ring

/-- The executable squared Gaussian ratio weight has the paper's exact
three-partition-function second moment. -/
theorem gaussianRatioWeight_secondMoment_eq (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 tau2 : ℝ}
    (hsigma2 : 0 < sigma2) (htau2 : 0 < tau2) :
    (∫ x, gaussianRatioWeight sigma2 tau2 x ^ 2
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))) =
      gaussianIntegral (truncatedBody q I)
          (sigma2 * tau2 / (2 * sigma2 - tau2)) /
        gaussianIntegral (truncatedBody q I) sigma2 := by
  rw [integral_truncatedGaussianProbability q I hsigma2]
  have hweighted :
      (∫ x in truncatedBody q I,
          gaussianRatioWeight sigma2 tau2 x ^ 2 * gaussianDensity sigma2 x) =
        gaussianIntegral (truncatedBody q I)
          (sigma2 * tau2 / (2 * sigma2 - tau2)) := by
    have hpaper := gaussianRatio_secondMomentIntegral q
      (truncatedVolumeInput q I) hsigma2 htau2
    simp only [truncatedVolumeInput_coe] at hpaper
    rw [← hpaper]
    apply setIntegral_congr_fun (truncatedBody_measurable q I)
    intro x hx
    change gaussianRatioWeight sigma2 tau2 x ^ 2 * gaussianDensity sigma2 x = _
    rw [gaussianRatioWeight_eq_sample q I sigma2 tau2 hx]
  rw [hweighted]
  ring

/-- The executable cubed Gaussian ratio weight has the exact normalized
third-moment partition-function formula. -/
theorem gaussianRatioWeight_thirdMoment_eq (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 tau2 : ℝ}
    (hsigma2 : 0 < sigma2) (htau2 : 0 < tau2) :
    (∫ x, gaussianRatioWeight sigma2 tau2 x ^ 3
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))) =
      gaussianIntegral (truncatedBody q I)
          (sigma2 * tau2 / (3 * sigma2 - 2 * tau2)) /
        gaussianIntegral (truncatedBody q I) sigma2 := by
  rw [integral_truncatedGaussianProbability q I hsigma2]
  have hweighted :
      (∫ x in truncatedBody q I,
          gaussianRatioWeight sigma2 tau2 x ^ 3 * gaussianDensity sigma2 x) =
        gaussianIntegral (truncatedBody q I)
          (sigma2 * tau2 / (3 * sigma2 - 2 * tau2)) := by
    have hpaper := gaussianRatio_thirdMomentIntegral q
      (truncatedVolumeInput q I) hsigma2 htau2
    simp only [truncatedVolumeInput_coe] at hpaper
    rw [← hpaper]
    apply setIntegral_congr_fun (truncatedBody_measurable q I)
    intro x hx
    change gaussianRatioWeight sigma2 tau2 x ^ 3 * gaussianDensity sigma2 x = _
    rw [gaussianRatioWeight_eq_sample q I sigma2 tau2 hx]
  rw [hweighted]
  ring

/-- The executable terminal weight has truncated ordinary volume divided by
the terminal Gaussian partition function as its stationary expectation. -/
theorem uniformRatioWeight_mean_eq (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (∫ x, uniformRatioWeight sigma2 x
        ∂(truncatedGaussianProbability q I sigma2 hsigma2 :
          Measure (AmbientSpace q.n))) =
      euclideanVolume (truncatedVolumeInput q I) /
        gaussianIntegral (truncatedBody q I) sigma2 := by
  rw [integral_truncatedGaussianProbability q I hsigma2]
  have hweighted :
      (∫ x in truncatedBody q I,
          uniformRatioWeight sigma2 x * gaussianDensity sigma2 x) =
        euclideanVolume (truncatedVolumeInput q I) := by
    rw [← uniformRatio_weightedIntegral q (truncatedVolumeInput q I) hsigma2]
    apply setIntegral_congr_fun (truncatedBody_measurable q I)
    intro x hx
    change uniformRatioWeight sigma2 x * gaussianDensity sigma2 x = _
    simp only [truncatedVolumeInput_coe]
    rw [uniformRatioWeight_eq_sample q I sigma2 hx]
  rw [hweighted]
  ring

end ArlibCommunity.Algorithms.CV18
