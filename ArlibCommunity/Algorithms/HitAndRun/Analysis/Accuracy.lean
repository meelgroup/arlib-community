/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.StepCompare
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Coupling
import ArlibCommunity.Algorithms.HitAndRun.Analysis.KernelTheorem

/-!
# Accuracy of the sampler

`hitAndRun_correct_proof`: after `m ≥ deadline n D M (ε/2)` steps from a start that is
`M`-warm outside a set of mass at most `ε/4`, the sampler's output law is within total
variation `ε` of the uniform law on the body.  Three parts:

* the exact lazy hit-and-run walk is within `ε/2` of uniform (`hitAndRun_mixes` at `ε/2`);
* the sampler's chain is within `m · M · ∫ β dπ + σ(S)` of the exact chain
  (`tvLe_iterate_split`, with the one-step comparison `stepKernel_compare`);
* the caps of `walkParams` make `m · M · ∫ β dπ ≤ ε/8`: the short-chord set has mass at most
  `n · 2D/2^k` (`target_shrunk_compl_le`), and `2^k`, `2^r` are large enough.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Foundations.MarkovChainTheory (iterate)

variable {n : ℕ}

/-- **The lazy version of a kernel keeps its invariant laws.** -/
theorem invariant_lazy {Ω : Type*} [MeasurableSpace Ω] {P : Kernel Ω Ω} {π : Measure Ω}
    (h : Kernel.Invariant P π) :
    Kernel.Invariant (ArlibCommunity.Foundations.MarkovChainTheory.lazy P) π := by
  ext S hS
  have hm : Measurable fun x => P x S := Kernel.measurable_coe P hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
  simp_rw [ArlibCommunity.Foundations.MarkovChainTheory.lazy_apply_set P _ hS]
  rw [lintegral_add_left (hm.const_mul _), lintegral_const_mul _ hm,
    lintegral_const_mul _ (measurable_one.indicator hS), lintegral_indicator_one hS]
  have hPS : ∫⁻ x, P x S ∂π = π S := by
    rw [← Measure.bind_apply hS (Kernel.aemeasurable _)]
    exact congrArg (· S) h
  rw [hPS, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- `2^⌈log₂ X⌉ ≥ X`. -/
theorem le_two_pow_ceil_logb {X : ℝ} (hX : 0 < X) : X ≤ 2 ^ ⌈Real.logb 2 X⌉₊ := by
  calc X = 2 ^ Real.logb 2 X := (Real.rpow_logb two_pos (by norm_num) hX).symm
    _ ≤ 2 ^ (⌈Real.logb 2 X⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = 2 ^ ⌈Real.logb 2 X⌉₊ := Real.rpow_natCast 2 _

/-- The mixing deadline is positive. -/
theorem deadline_pos [NeZero n] (hn : 1 ≤ n) (p : Problem n) {M ε : ℝ} (hM : 1 ≤ M)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) : 0 < deadline n p.diameter M (ε / 2) := by
  have hD := diameter_pos p
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (8 * M / (ε / 2) ^ 2) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  unfold deadline
  positivity

/-- **The caps' arithmetic.**  With the parameters `walkParams n D M ε m` (`m ≥ 1`), the
bisection's final gap `δ = 2D/2^k` satisfies `n · δ ≤ ε/(8mM)` and `δ < 1`, and
`(1/2)^r ≤ ε/(8mM)`. -/
theorem walkParams_caps {D M ε : ℝ} (hD : 0 < D) (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let w := walkParams n D M ε m
    (n : ℝ) * (2 * w.D / 2 ^ w.bisectionSteps) ≤ ε / (8 * m * M) ∧
      2 * w.D / 2 ^ w.bisectionSteps < 1 ∧
      (1 / 2 : ℝ) ^ w.rejectionTries ≤ ε / (8 * m * M) := by
  intro w
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX1 : 0 < 16 * m * M * n * D / ε := by positivity
  have hX2 : 0 < 8 * m * M / ε := by positivity
  have hk := le_two_pow_ceil_logb hX1
  have hr := le_two_pow_ceil_logb hX2
  change 16 * m * M * n * D / ε ≤ 2 ^ w.bisectionSteps at hk
  change 8 * m * M / ε ≤ 2 ^ w.rejectionTries at hr
  have hpow : (0 : ℝ) < 2 ^ w.bisectionSteps := by positivity
  have hwD : w.D = D := rfl
  have hδ : (n : ℝ) * (2 * w.D / 2 ^ w.bisectionSteps) ≤ ε / (8 * m * M) := by
    rw [hwD, mul_div_assoc', div_le_div_iff₀ hpow (by positivity)]
    rw [div_le_iff₀ hε0] at hk
    nlinarith
  refine ⟨hδ, ?_, ?_⟩
  · have : ε / (8 * m * M) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : 2 * w.D / 2 ^ w.bisectionSteps ≤ (n : ℝ) * (2 * w.D / 2 ^ w.bisectionSteps) :=
      le_mul_of_one_le_left (by rw [hwD]; positivity) hn'
    linarith
  · rw [one_div, inv_pow, inv_le_comm₀ (by positivity) (by positivity), inv_div]
    exact hr

/-- **Accuracy of the sampler.** -/
theorem hitAndRun_correct_proof (hn : 2 ≤ n) (p : Problem n) (oracle : MembershipOracle p)
    {σ : Measure (State n)} [IsProbabilityMeasure σ]
    {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {S : Set (State n)} (hWarm : WarmStart p.body σ M (ε / 2) S)
    {m : ℕ} (hm : deadline n p.diameter M (ε / 2) ≤ (m : ℝ)) :
    TVLe (walkLaw (walkParams n p.diameter M ε m) oracle σ) (target p.body)
      (ENNReal.ofReal ε) := by
  have : NeZero n := ⟨by omega⟩
  set w := walkParams n p.diameter M ε m with hwdef
  have hmeas := measurable_member p.measurable_body oracle.correct
  have hexact := TheoremProof.hitAndRun_mixes hn p hM (half_pos hε0) (by linarith) hWarm hm
  have hm1 : 1 ≤ m := by
    have := (deadline_pos (by omega) p hM hε0 hε1).trans_le hm
    exact_mod_cast this
  obtain ⟨hδn, hδ1, hr⟩ := walkParams_caps (n := n) (diameter_pos p) hM hε0 hε1 hm1
    (by omega)
  change (n : ℝ) * (2 * w.D / 2 ^ w.bisectionSteps) ≤ ε / (8 * m * M) at hδn
  change 2 * w.D / 2 ^ w.bisectionSteps < 1 at hδ1
  change (1 / 2 : ℝ) ^ w.rejectionTries ≤ ε / (8 * m * M) at hr
  have hD : w.D = p.diameter := rfl
  obtain ⟨hSm, hSmass, hdom⟩ := hWarm
  have hclose : ∀ x A, MeasurableSet A →
      stepKernel w oracle.query hmeas x A ≤ lazyStep p.body x A + stepGap p w x ∧
        lazyStep p.body x A ≤ stepKernel w oracle.query hmeas x A + stepGap p w x :=
    fun x A hA => stepKernel_compare p oracle hmeas w hD hδ1.le x hA
  have hwarm : ArlibCommunity.Foundations.Convex.IsWarm (ENNReal.ofReal M)
      (σ.restrict Sᶜ) (target p.body) := fun A hA => by
    rw [Measure.restrict_apply hA, ← sdiff_eq]
    exact hdom A hA
  have hinv : Kernel.Invariant (lazyStep p.body) (target p.body) :=
    invariant_lazy (PseudocodeProof.target_invariant p.measurable_body)
  have : IsMarkovKernel (lazyStep p.body) := by unfold lazyStep step; infer_instance
  have hsplit := tvLe_iterate_split (stepKernel w oracle.query hmeas) (lazyStep p.body)
    (measurable_stepGap p w hδ1) hclose σ hSm hwarm hinv m
  -- the integral of the gap
  have htprob : IsProbabilityMeasure (target p.body) := by
    rw [target_eq_uniformOn]
    refine ArlibCommunity.Foundations.Convex.isProbabilityMeasure_uniformOn _ ?_
      p.bounded_body.measure_lt_top.ne
    intro h
    have := measure_mono (μ := volume) p.unitBall_subset
    rw [h, nonpos_iff_eq_zero] at this
    exact (Metric.measure_closedBall_pos volume p.center one_pos).ne' this
  have hδ0 : 0 ≤ 2 * w.D / 2 ^ w.bisectionSteps := by
    have := diameter_pos p; rw [← hD] at this; positivity
  have hgapInt : ∫⁻ x, stepGap p w x ∂(target p.body) ≤
      2⁻¹ * (ENNReal.ofReal (n * (2 * w.D / 2 ^ w.bisectionSteps)) + 2⁻¹ ^ w.rejectionTries) := by
    have hmS := (measurableSet_shrunk (c := p.center) p.measurable_body hδ1).compl
    have hind : Measurable fun x => (shrunk p.body p.center
        (2 * w.D / 2 ^ w.bisectionSteps))ᶜ.indicator (1 : State n → ℝ≥0∞) x :=
      measurable_one.indicator hmS
    unfold stepGap
    rw [lintegral_const_mul (2⁻¹ : ℝ≥0∞) (f := fun x => (shrunk p.body p.center
        (2 * w.D / 2 ^ w.bisectionSteps))ᶜ.indicator (1 : State n → ℝ≥0∞) x +
          2⁻¹ ^ w.rejectionTries) (hind.add measurable_const),
      lintegral_add_right _ measurable_const, lintegral_indicator_one hmS, lintegral_const,
      measure_univ, mul_one]
    gcongr
    exact target_shrunk_compl_le p.measurable_body p.convex_body p.bounded_body
      p.unitBall_subset hδ0 hδ1
  -- the caps' error
  have hcap : (m : ℝ≥0∞) * (ENNReal.ofReal M * ∫⁻ x, stepGap p w x ∂(target p.body)) ≤
      ENNReal.ofReal (ε / 4) := by
    have hc : (2⁻¹ : ℝ≥0∞) ^ w.rejectionTries = ENNReal.ofReal ((1 / 2) ^ w.rejectionTries) := by
      rw [ENNReal.ofReal_pow (by norm_num), ArlibCommunity.Foundations.MarkovChainTheory.ofReal_one_half,
        one_div]
    have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
      rw [ArlibCommunity.Foundations.MarkovChainTheory.ofReal_one_half, one_div]
    calc (m : ℝ≥0∞) * (ENNReal.ofReal M * ∫⁻ x, stepGap p w x ∂(target p.body))
        ≤ (m : ℝ≥0∞) * (ENNReal.ofReal M *
            (2⁻¹ * (ENNReal.ofReal (n * (2 * w.D / 2 ^ w.bisectionSteps)) + 2⁻¹ ^ w.rejectionTries))) := by gcongr
      _ = ENNReal.ofReal (m * (M * (1 / 2 * (n * (2 * w.D / 2 ^ w.bisectionSteps) + (1 / 2) ^ w.rejectionTries)))) := by
          rw [hc, h2, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by linarith),
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (ε / 4) := by
          apply ENNReal.ofReal_le_ofReal
          have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          have hsum : (n : ℝ) * (2 * w.D / 2 ^ w.bisectionSteps) + (1 / 2) ^ w.rejectionTries ≤ 2 * (ε / (8 * m * M)) := by
            linarith
          calc (m : ℝ) * (M * (1 / 2 * (n * (2 * w.D / 2 ^ w.bisectionSteps) + (1 / 2) ^ w.rejectionTries)))
              ≤ m * (M * (1 / 2 * (2 * (ε / (8 * m * M))))) := by gcongr
            _ = ε / 8 := by field_simp
            _ ≤ ε / 4 := by linarith
  have htotal := hsplit.trans hexact
  have hsum : (m : ℝ≥0∞) * (ENNReal.ofReal M * ∫⁻ x, stepGap p w x ∂(target p.body)) + σ S +
      ENNReal.ofReal (ε / 2) ≤ ENNReal.ofReal ε := by
    calc _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 2 / 2) + ENNReal.ofReal (ε / 2) := by
          gcongr
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  rw [walkLaw_eq_iterate w oracle hmeas σ]
  exact fun A hA => (htotal.mono hsum) A hA

end ArlibCommunity.Algorithms.HitAndRun
