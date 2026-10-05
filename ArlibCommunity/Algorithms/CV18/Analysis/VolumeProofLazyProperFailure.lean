/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperProgram
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyGaussianConductance

/-!
# Failure bounds for the executable CV18 proper-step counter

This module proves a direct Markov cutoff inequality for the actual finite
membership-oracle recursion. A Bellman potential avoids identifying every
stopped-path cylinder with the independently restarted trajectory model.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem measurableSet_option_none {S : Type*} [MeasurableSpace S] :
    MeasurableSet ({none} : Set (Option S)) := by
  rw [show ({none} : Set (Option S)) = Option.isSome ⁻¹' {false} by
    ext value
    cases value <;> simp]
  exact measurable_optionIsSome (measurableSet_singleton false)

theorem cappedProperMarkedLaw_isProbabilityMeasure
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) [IsMarkovKernel Q] : ∀ rawCap properSteps current,
    IsProbabilityMeasure (cappedProperMarkedLaw Q rawCap properSteps current) := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro properSteps current
      cases properSteps <;> simp only [cappedProperMarkedLaw] <;> infer_instance
  | succ rawCap ih =>
      intro properSteps current
      cases properSteps with
      | zero =>
          simp only [cappedProperMarkedLaw]
          infer_instance
      | succ properSteps =>
          simp only [cappedProperMarkedLaw]
          have hnext : Measurable fun result : Bool × S =>
              cappedProperMarkedLaw Q rawCap
                (if result.1 then properSteps else properSteps + 1) result.2 := by
            rw [show (fun result : Bool × S =>
                cappedProperMarkedLaw Q rawCap
                  (if result.1 then properSteps else properSteps + 1) result.2) =
              fun result => if result.1 = true then
                cappedProperMarkedLaw Q rawCap properSteps result.2 else
                cappedProperMarkedLaw Q rawCap (properSteps + 1) result.2 by
              funext result
              rcases result with ⟨mark, state⟩
              cases mark <;> rfl]
            exact Measurable.ite (measurable_fst (measurableSet_singleton true))
              ((measurable_cappedProperMarkedLaw Q rawCap properSteps).comp measurable_snd)
              ((measurable_cappedProperMarkedLaw Q rawCap (properSteps + 1)).comp
                measurable_snd)
          apply MeasureTheory.isProbabilityMeasure_bind hnext.aemeasurable
          filter_upwards with result
          rcases result with ⟨mark, state⟩
          cases mark <;> exact ih _ state

theorem cappedProperMarkedLaw_apply_none_succ
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) (rawCap properSteps : ℕ) (current : S) :
    cappedProperMarkedLaw Q (rawCap + 1) (properSteps + 1) current {none} =
      ∫⁻ result, cappedProperMarkedLaw Q rawCap
        (if result.1 then properSteps else properSteps + 1) result.2 {none}
        ∂Q current := by
  simp only [cappedProperMarkedLaw]
  rw [Measure.bind_apply measurableSet_option_none]
  have hmeas : Measurable fun result : Bool × S =>
      cappedProperMarkedLaw Q rawCap
        (if result.1 then properSteps else properSteps + 1) result.2 := by
    rw [show (fun result : Bool × S =>
        cappedProperMarkedLaw Q rawCap
          (if result.1 then properSteps else properSteps + 1) result.2) =
      fun result => if result.1 = true then
        cappedProperMarkedLaw Q rawCap properSteps result.2 else
        cappedProperMarkedLaw Q rawCap (properSteps + 1) result.2 by
      funext result
      rcases result with ⟨mark, state⟩
      cases mark <;> rfl]
    exact Measurable.ite (measurable_fst (measurableSet_singleton true))
      ((measurable_cappedProperMarkedLaw Q rawCap properSteps).comp measurable_snd)
      ((measurable_cappedProperMarkedLaw Q rawCap (properSteps + 1)).comp measurable_snd)
  exact hmeas.aemeasurable

/-- Abstract Markov inequality for the finite proper-mark counter. Any
measurable potential paying one unit for the next raw transition bounds the
probability that the counter exhausts its raw cap. -/
theorem natCast_mul_cappedProperMarkedLaw_none_le
    {S : Type*} [MeasurableSpace S]
    (Q : Kernel S (Bool × S)) [IsMarkovKernel Q]
    (E : ℕ → S → ℝ≥0∞)
    (hEzero : ∀ current, E 0 current = 0)
    (hstep : ∀ properSteps current,
      1 + ∫⁻ result, E (if result.1 then properSteps else properSteps + 1) result.2
          ∂Q current ≤ E (properSteps + 1) current) :
    ∀ (rawCap properSteps : ℕ) (current : S),
      (rawCap : ℝ≥0∞) * cappedProperMarkedLaw Q rawCap properSteps current {none} ≤
        E properSteps current := by
  intro rawCap
  induction rawCap with
  | zero =>
      intro properSteps current
      simp
  | succ rawCap ih =>
      intro properSteps current
      cases properSteps with
      | zero =>
          rw [hEzero]
          simp only [cappedProperMarkedLaw, nonpos_iff_eq_zero]
          rw [Measure.dirac_apply' _ measurableSet_option_none]
          simp
      | succ properSteps =>
          let f : Bool × S → ℝ≥0∞ := fun result =>
            cappedProperMarkedLaw Q rawCap
              (if result.1 then properSteps else properSteps + 1) result.2 {none}
          let e : Bool × S → ℝ≥0∞ := fun result =>
            E (if result.1 then properSteps else properSteps + 1) result.2
          have hf_le_one : ∀ result, f result ≤ 1 := by
            intro result
            let _ : IsProbabilityMeasure
                (cappedProperMarkedLaw Q rawCap
                  (if result.1 then properSteps else properSteps + 1) result.2) :=
              cappedProperMarkedLaw_isProbabilityMeasure Q _ _ _
            exact (measure_mono (Set.subset_univ {none})).trans_eq measure_univ
          have hcap : (rawCap : ℝ≥0∞) * (∫⁻ result, f result ∂Q current) ≤
              ∫⁻ result, e result ∂Q current := by
            rw [← lintegral_const_mul' (rawCap : ℝ≥0∞) f (by simp)]
            apply lintegral_mono
            intro result
            exact ih _ _
          have hfint : (∫⁻ result, f result ∂Q current) ≤ 1 := by
            calc
              (∫⁻ result, f result ∂Q current) ≤
                  ∫⁻ _result, (1 : ℝ≥0∞) ∂Q current :=
                lintegral_mono hf_le_one
              _ = 1 := by simp
          rw [cappedProperMarkedLaw_apply_none_succ]
          change ((rawCap + 1 : ℕ) : ℝ≥0∞) * (∫⁻ result, f result ∂Q current) ≤ _
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          calc
            (rawCap : ℝ≥0∞) * (∫⁻ result, f result ∂Q current) +
                ∫⁻ result, f result ∂Q current ≤
              (∫⁻ result, e result ∂Q current) + 1 := add_le_add hcap hfint
            _ = 1 + ∫⁻ result, e result ∂Q current := add_comm _ _
            _ ≤ E (properSteps + 1) current := hstep properSteps current

end ArlibCommunity.Algorithms.CV18

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Bellman potential for the number of raw marked proposals needed to obtain
the requested number of proper proposals. It is totalized to `∞` off `K`,
where the executable proper clock is not intended to start. -/
noncomputable def totalLazyProperExpectedRawCost
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) : ℕ → EuclideanSpace ℝ (Fin n) → ℝ≥0∞
  | 0, _ => 0
  | properSteps + 1, current =>
      if current ∈ K then
        (ell K delta current)⁻¹ +
          ∫⁻ next, totalLazyProperExpectedRawCost K hK delta s properSteps next
            ∂lazy (speedyMetropolisGaussian K delta s) current
      else ⊤

theorem measurable_totalLazyProperExpectedRawCost
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) : ∀ properSteps,
    Measurable (totalLazyProperExpectedRawCost K hK delta s properSteps) := by
  intro properSteps
  induction properSteps with
  | zero => exact measurable_const
  | succ properSteps ih =>
      simp only [totalLazyProperExpectedRawCost]
      apply Measurable.ite hK
      · exact (Measurable.inv (measurable_ell hK delta)).add ih.lintegral_kernel
      · exact measurable_const

theorem totalLazyProperExpectedRawCost_zero
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ) (current : EuclideanSpace ℝ (Fin n)) :
    totalLazyProperExpectedRawCost K hK delta s 0 current = 0 := rfl

/-- The expected-cost potential pays for one executable raw marked step. -/
theorem one_add_lintegral_totalLazyProperExpectedRawCost_le
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {delta : ℝ} (hdelta : 0 < delta) (s : ℝ)
    (properSteps : ℕ) (current : EuclideanSpace ℝ (Fin n)) :
    1 + ∫⁻ result,
        totalLazyProperExpectedRawCost K hK delta s
          (if result.1 then properSteps else properSteps + 1) result.2
        ∂lazyProperProposalGaussianAux K hK delta s current ≤
      totalLazyProperExpectedRawCost K hK delta s (properSteps + 1) current := by
  by_cases hx : current ∈ K
  · let p := ell K delta current
    let P := lazy (speedyMetropolisGaussian K delta s)
    let A : ℝ≥0∞ := ∫⁻ next,
      totalLazyProperExpectedRawCost K hK delta s properSteps next ∂P current
    let B : ℝ≥0∞ := totalLazyProperExpectedRawCost K hK delta s
      (properSteps + 1) current
    have hp0 : p ≠ 0 := by
      change ell K delta current ≠ 0
      exact (ENNReal.toReal_pos_iff.mp
        (ell_toReal_pos_of_convex hKc hKb hK0 hdelta current hx)).1.ne'
    have hp1 : p ≤ 1 := ell_le_one K delta current
    have hptop : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
    have hB : B = p⁻¹ + A := by
      simp [B, A, p, P, totalLazyProperExpectedRawCost, hx]
    let g : Bool × EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun result =>
      totalLazyProperExpectedRawCost K hK delta s
        (if result.1 then properSteps else properSteps + 1) result.2
    have hg : Measurable g := by
      rw [show g = fun result => if result.1 = true then
          totalLazyProperExpectedRawCost K hK delta s properSteps result.2 else
          totalLazyProperExpectedRawCost K hK delta s (properSteps + 1) result.2 by
        funext result
        rcases result with ⟨mark, state⟩
        cases mark <;> rfl]
      exact Measurable.ite (measurable_fst (measurableSet_singleton true))
        ((measurable_totalLazyProperExpectedRawCost K hK delta s properSteps).comp
          measurable_snd)
        ((measurable_totalLazyProperExpectedRawCost K hK delta s (properSteps + 1)).comp
          measurable_snd)
    have hlin : (∫⁻ result, g result
          ∂lazyProperProposalGaussianAux K hK delta s current) =
        p * A + (1 - p) * B := by
      have htrue : Measurable
          (fun y : EuclideanSpace ℝ (Fin n) => (true, y)) := by fun_prop
      change (∫⁻ result, g result ∂(p • (P current).map (fun y => (true, y)) +
          (1 - p) • Measure.dirac (false, current))) = _
      rw [lintegral_add_measure, lintegral_smul_measure,
        lintegral_smul_measure,
        lintegral_map hg htrue,
        lintegral_dirac' _ hg]
      simp only [g, if_true, smul_eq_mul]
      rfl
    rw [show (fun result => totalLazyProperExpectedRawCost K hK delta s
          (if result.1 then properSteps else properSteps + 1) result.2) = g from rfl,
      hlin, hB]
    have hpinv : p * p⁻¹ = 1 := ENNReal.mul_inv_cancel hp0 hptop
    have hpsum : p + (1 - p) = 1 := add_tsub_cancel_of_le hp1
    calc
      1 + (p * A + (1 - p) * (p⁻¹ + A)) =
          (p + (1 - p)) * p⁻¹ + (p + (1 - p)) * A := by
            rw [← hpinv]
            ring
      _ = p⁻¹ + A := by rw [hpsum, one_mul, one_mul]
      _ = B := hB.symm
      _ ≤ totalLazyProperExpectedRawCost K hK delta s
          (properSteps + 1) current := le_rfl
  · simp [totalLazyProperExpectedRawCost, hx]

/-- From an `M`-warm start, the Bellman potential is bounded by the same
stationary reciprocal-local-conductance mean used in CV18's wasted-step
calculation. -/
theorem lintegral_totalLazyProperExpectedRawCost_le_of_isWarm
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (delta s : ℝ)
    (pi : Measure (EuclideanSpace ℝ (Fin n)))
    (hpiK : pi Kᶜ = 0)
    (hpi : Kernel.Invariant (lazy (speedyMetropolisGaussian K delta s)) pi)
    {M : ℝ≥0∞} {mu : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm M mu pi) : ∀ properSteps,
    ∫⁻ current, totalLazyProperExpectedRawCost K hK delta s properSteps current ∂mu ≤
      (properSteps : ℝ≥0∞) *
        (M * ∫⁻ current, (ell K delta current)⁻¹ ∂pi) := by
  intro properSteps
  induction properSteps generalizing mu with
  | zero => simp [totalLazyProperExpectedRawCost]
  | succ properSteps ih =>
      let P := lazy (speedyMetropolisGaussian K delta s)
      let E := totalLazyProperExpectedRawCost K hK delta s
      have hmuKc : mu Kᶜ = 0 := by
        apply le_zero_iff.mp
        calc
          mu Kᶜ ≤ M * pi Kᶜ := hwarm Kᶜ hK.compl
          _ = 0 := by rw [hpiK, mul_zero]
      have hmuK : ∀ᵐ current ∂mu, current ∈ K := by
        rw [show (∀ᵐ current ∂mu, current ∈ K) ↔ K ∈ ae mu from Iff.rfl,
          mem_ae_iff]
        exact hmuKc
      have hrec : (∫⁻ current, E (properSteps + 1) current ∂mu) =
          (∫⁻ current, (ell K delta current)⁻¹ ∂mu) +
            ∫⁻ current, E properSteps current ∂step P mu := by
        calc
          (∫⁻ current, E (properSteps + 1) current ∂mu) =
              ∫⁻ current, (ell K delta current)⁻¹ +
                (∫⁻ next, E properSteps next ∂P current) ∂mu := by
            apply lintegral_congr_ae
            filter_upwards [hmuK] with current hx
            simp [E, P, totalLazyProperExpectedRawCost, hx]
          _ = (∫⁻ current, (ell K delta current)⁻¹ ∂mu) +
                ∫⁻ current, (∫⁻ next, E properSteps next ∂P current) ∂mu := by
            exact lintegral_add_left
              ((measurable_ell hK delta).inv) _
          _ = (∫⁻ current, (ell K delta current)⁻¹ ∂mu) +
                ∫⁻ current, E properSteps current ∂step P mu := by
            rw [step, Measure.lintegral_bind (Kernel.measurable P).aemeasurable
              (measurable_totalLazyProperExpectedRawCost K hK delta s
                properSteps).aemeasurable]
      rw [hrec]
      calc
        (∫⁻ current, (ell K delta current)⁻¹ ∂mu) +
            ∫⁻ current, E properSteps current ∂step P mu ≤
          M * (∫⁻ current, (ell K delta current)⁻¹ ∂pi) +
            (properSteps : ℝ≥0∞) *
              (M * ∫⁻ current, (ell K delta current)⁻¹ ∂pi) := by
                apply add_le_add
                · exact lintegral_le_of_isWarm hwarm _
                · exact ih (isWarm_step hwarm (step_invariant hpi))
        _ = ((properSteps + 1 : ℕ) : ℝ≥0∞) *
              (M * ∫⁻ current, (ell K delta current)⁻¹ ∂pi) := by
            rw [Nat.cast_add, Nat.cast_one]
            ring

/-- Pointwise failure bound for the concrete lazy proper-proposal marked
kernel. -/
theorem natCast_mul_cappedLazyProperMarkedLaw_none_le
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {delta : ℝ} (hdelta : 0 < delta) (s : ℝ)
    (rawCap properSteps : ℕ) (current : EuclideanSpace ℝ (Fin n)) :
    (rawCap : ℝ≥0∞) *
        ArlibCommunity.Algorithms.CV18.cappedProperMarkedLaw
          (lazyProperProposalGaussianAux K hK delta s)
          rawCap properSteps current {none} ≤
      totalLazyProperExpectedRawCost K hK delta s properSteps current := by
  exact ArlibCommunity.Algorithms.CV18.natCast_mul_cappedProperMarkedLaw_none_le
    (lazyProperProposalGaussianAux K hK delta s)
    (totalLazyProperExpectedRawCost K hK delta s)
    (totalLazyProperExpectedRawCost_zero K hK delta s)
    (one_add_lintegral_totalLazyProperExpectedRawCost_le
      K hK hKc hKb hK0 hdelta s) rawCap properSteps current

/-- Warm-start Markov cutoff for the actual finite marked recursion. Unlike
the earlier trajectory theorem, its left side is exactly the failure mass of
`cappedProperMarkedLaw`. -/
theorem mul_natCast_mul_bind_cappedLazyProperMarkedLaw_none_le
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {delta : ℝ} (hdelta : 0 < delta) (variance : ℝ)
    (hZ0 : ellGaussianMeasure K delta variance Set.univ ≠ 0)
    (hZtop : ellGaussianMeasure K delta variance Set.univ ≠ ⊤)
    {lambda M : ℝ≥0∞}
    (hlambda : lambda * (∫⁻ x in K, gaussianWeight variance x) ≤
      ellGaussianMeasure K delta variance Set.univ)
    {mu : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm M mu (ellGaussianProb K delta variance))
    (rawCap properSteps : ℕ) :
    lambda * (rawCap : ℝ≥0∞) *
        (mu.bind fun current =>
          ArlibCommunity.Algorithms.CV18.cappedProperMarkedLaw
            (lazyProperProposalGaussianAux K hK delta variance)
            rawCap properSteps current) {none} ≤
      (properSteps : ℝ≥0∞) * M := by
  let Q := lazyProperProposalGaussianAux K hK delta variance
  let E := totalLazyProperExpectedRawCost K hK delta variance
  let pi := ellGaussianProb K delta variance
  have hbind : (mu.bind fun current =>
        ArlibCommunity.Algorithms.CV18.cappedProperMarkedLaw Q
          rawCap properSteps current) {none} =
      ∫⁻ current, ArlibCommunity.Algorithms.CV18.cappedProperMarkedLaw Q
        rawCap properSteps current {none} ∂mu := by
    rw [Measure.bind_apply
      ArlibCommunity.Algorithms.CV18.measurableSet_option_none]
    exact (ArlibCommunity.Algorithms.CV18.measurable_cappedProperMarkedLaw
      Q rawCap properSteps).aemeasurable
  have hfailure : (rawCap : ℝ≥0∞) *
        (mu.bind fun current =>
          ArlibCommunity.Algorithms.CV18.cappedProperMarkedLaw Q
            rawCap properSteps current) {none} ≤
      ∫⁻ current, E properSteps current ∂mu := by
    rw [hbind, ← lintegral_const_mul' (rawCap : ℝ≥0∞) _ (by simp)]
    apply lintegral_mono
    intro current
    exact natCast_mul_cappedLazyProperMarkedLaw_none_le
      K hK hKc hKb hK0 hdelta variance rawCap properSteps current
  have hcost : (∫⁻ current, E properSteps current ∂mu) ≤
      (properSteps : ℝ≥0∞) *
        (M * ∫⁻ current, (ell K delta current)⁻¹ ∂pi) := by
    exact lintegral_totalLazyProperExpectedRawCost_le_of_isWarm K hK delta variance pi
      (ellGaussianProb_compl_eq_zero hK delta variance)
      (isReversible_lazy
        (isReversible_speedyMetropolisGaussian_prob hK delta variance)).invariant
      hwarm properSteps
  have hstationary : lambda *
      (∫⁻ current, (ell K delta current)⁻¹ ∂pi) ≤ 1 :=
    mul_lintegral_inv_ell_ellGaussianProb_le_one
      hK hdelta variance hZ0 hZtop hlambda
  calc
    lambda * (rawCap : ℝ≥0∞) *
        (mu.bind fun current =>
          ArlibCommunity.Algorithms.CV18.cappedProperMarkedLaw Q
            rawCap properSteps current) {none} =
      lambda * ((rawCap : ℝ≥0∞) *
        (mu.bind fun current =>
          ArlibCommunity.Algorithms.CV18.cappedProperMarkedLaw Q
            rawCap properSteps current) {none}) := by ring
    _ ≤ lambda * (∫⁻ current, E properSteps current ∂mu) := by gcongr
    _ ≤ lambda * ((properSteps : ℝ≥0∞) *
        (M * ∫⁻ current, (ell K delta current)⁻¹ ∂pi)) := by gcongr
    _ = (properSteps : ℝ≥0∞) * M *
        (lambda * ∫⁻ current, (ell K delta current)⁻¹ ∂pi) := by ring
    _ ≤ (properSteps : ℝ≥0∞) * M * 1 := by gcongr
    _ = (properSteps : ℝ≥0∞) * M := mul_one _

end Arlib.MarkovChains

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Arlib Arlib.MarkovChains
open scoped ENNReal

/-- The paper's advertised `1/2` average-conductance cutoff bound, now stated
for the failure output of the actual capped membership-oracle program. -/
theorem half_mul_natCast_mul_cappedProperMetropolisBallWalk_none_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M : ℝ≥0∞} {mu : Measure (AmbientSpace q.n)}
    (hwarm : IsWarm M mu
      (ellGaussianProb (truncatedBody q I)
        (figureOneProposalRadius q sigma2) sigma2))
    (rawCap properSteps : ℕ) :
    ENNReal.ofReal (1 / 2) * (rawCap : ℝ≥0∞) *
        (mu.bind fun current =>
          (cappedProperMetropolisBallWalk q sigma2 rawCap properSteps current).runEstimate
            oracle.query) {none} ≤
      (properSteps : ℝ≥0∞) * M := by
  let K := truncatedBody q I
  let delta := figureOneProposalRadius q sigma2
  have hK : MeasurableSet K := truncatedBody_measurable q I
  have hKc : Convex ℝ K := (truncatedVolumeInput q I).body.convex
  have hKcompact : IsCompact K := (truncatedVolumeInput q I).body.isCompact
  have hKb : Bornology.IsBounded K := hKcompact.isBounded
  have hK0 : volume K ≠ 0 := by
    apply ne_of_gt
    have hballpos : 0 < volume (ball (0 : AmbientSpace q.n) 1) :=
      Metric.measure_ball_pos volume 0 (by norm_num)
    exact hballpos.trans_le (measure_mono fun x hx =>
      unitBall_subset_truncatedBody q I (Metric.ball_subset_closedBall hx))
  have hdelta : 0 < delta := figureOneProposalRadius_pos q hsigma2
  have hZ0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 :=
    ellGaussianMeasure_univ_ne_zero hK hKc hKb hK0 hdelta sigma2
  have hZtop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ :=
    ellGaussianMeasure_ne_top_cv18 hKcompact.measure_lt_top.ne delta hsigma2
  have hlambda : ENNReal.ofReal (1 / 2) *
      (∫⁻ x in K, gaussianWeight sigma2 x) ≤
        ellGaussianMeasure K delta sigma2 Set.univ := by
    exact half_mul_lintegral_gaussianWeight_le_figureOne q I hsigma2
  have hlaw : (fun current =>
        (cappedProperMetropolisBallWalk q sigma2 rawCap properSteps current).runEstimate
          oracle.query) =
      fun current => cappedProperMarkedLaw
        (lazyProperProposalGaussianAux K hK delta sigma2)
        rawCap properSteps current := by
    funext current
    exact (cappedProperMetropolisBallWalk_semantics
      q I oracle hsigma2 rawCap properSteps).2.2 current
  rw [hlaw]
  exact mul_natCast_mul_bind_cappedLazyProperMarkedLaw_none_le
    K hK hKc hKb hK0 hdelta sigma2 hZ0 hZtop hlambda hwarm rawCap properSteps

end ArlibCommunity.Algorithms.CV18
