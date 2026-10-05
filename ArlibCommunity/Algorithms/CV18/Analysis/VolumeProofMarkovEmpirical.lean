/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.L2Mixing

/-!
# Empirical averages along warm Markov trajectories

CV18 reuses the last point of a phase and obtains the ratio samples from one
trajectory.  The samples are therefore not independent.  This module supplies
the trajectory domination and covariance estimates needed to formalize the
paper's dependent-sample argument.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- Law of the current state and the sum of the next `samples` observations.
This finite accumulator is exactly the object used by CV18's ratio estimator
and avoids introducing an irrelevant infinite trajectory. -/
noncomputable def markovSumLaw (P : Kernel S S) (f : S → ℝ) :
    ℕ → Measure S → Measure (S × ℝ)
  | 0, mu => mu.map fun x => (x, 0)
  | samples + 1, mu =>
      (markovSumLaw P f samples mu).bind fun stateSum =>
        (P stateSum.1).map fun next => (next, stateSum.2 + f next)

theorem measurable_markovSumStep (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) :
    Measurable fun stateSum : S × ℝ =>
      (P stateSum.1).map fun next => (next, stateSum.2 + f next) := by
  apply ArlibCommunity.Algorithms.CV18.measurable_measure_map_param_variable
  · exact P.measurable.comp measurable_fst
  · intro stateSum
    infer_instance
  exact measurable_snd.prodMk
    ((measurable_snd.comp measurable_fst).add (hf.comp measurable_snd))

/-- The accumulator update as a Markov kernel. -/
noncomputable def markovSumKernel (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (hf : Measurable f) : Kernel (S × ℝ) (S × ℝ) :=
  ⟨fun stateSum =>
      (P stateSum.1).map fun next => (next, stateSum.2 + f next),
    measurable_markovSumStep P hf⟩

instance markovSumKernel_isMarkovKernel
    (P : Kernel S S) [IsMarkovKernel P] (f : S → ℝ) (hf : Measurable f) :
    IsMarkovKernel (markovSumKernel P f hf) :=
  ⟨fun _ => Measure.isProbabilityMeasure_map (by fun_prop)⟩

@[simp] theorem markovSumKernel_apply
    (P : Kernel S S) [IsMarkovKernel P] (f : S → ℝ) (hf : Measurable f)
    (stateSum : S × ℝ) :
    markovSumKernel P f hf stateSum =
      (P stateSum.1).map fun next => (next, stateSum.2 + f next) := rfl

theorem markovSumLaw_succ_eq_comp
    (P : Kernel S S) [IsMarkovKernel P] (f : S → ℝ) (hf : Measurable f)
    (samples : ℕ) (mu : Measure S) :
    markovSumLaw P f (samples + 1) mu =
      markovSumKernel P f hf ∘ₘ markovSumLaw P f samples mu := rfl

theorem markovSumLaw_isProbabilityMeasure
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) (mu : Measure S) [IsProbabilityMeasure mu] :
    ∀ samples, IsProbabilityMeasure (markovSumLaw P f samples mu) := by
  intro samples
  induction samples with
  | zero =>
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  | succ samples ih =>
      simp only [markovSumLaw]
      let _ : IsProbabilityMeasure (markovSumLaw P f samples mu) := ih
      apply MeasureTheory.isProbabilityMeasure_bind
        (measurable_markovSumStep P hf).aemeasurable
      filter_upwards with stateSum
      exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Product-kernel form of one accumulator update.  This is equivalent to
`markovSumLaw_succ_eq_comp`, but supports a substantially smaller specialized
Fubini proof term for real moments. -/
theorem markovSumLaw_succ_eq_map_compProd
    (P : Kernel S S) [IsMarkovKernel P] (f : S → ℝ) (hf : Measurable f)
    (samples : ℕ) (mu : Measure S) [IsProbabilityMeasure mu] :
    markovSumLaw P f (samples + 1) mu =
      ((markovSumLaw P f samples mu) ⊗ₘ
        (P.comap Prod.fst measurable_fst)).map
          (fun p => (p.2, p.1.2 + f p.2)) := by
  let _ : IsProbabilityMeasure (markovSumLaw P f samples mu) :=
    markovSumLaw_isProbabilityMeasure P hf mu samples
  ext A hA
  rw [markovSumLaw]
  have hQ : Measurable fun stateSum : S × ℝ =>
      (P stateSum.1).map fun next => (next, stateSum.2 + f next) :=
    measurable_markovSumStep P hf
  rw [Measure.bind_apply hA hQ.aemeasurable]
  have htransform : Measurable (fun p : (S × ℝ) × S =>
      (p.2, p.1.2 + f p.2)) := by fun_prop
  rw [Measure.map_apply htransform hA,
    Measure.compProd_apply (htransform hA)]
  congr with stateSum
  rw [Kernel.comap_apply]
  rw [Measure.map_apply (by fun_prop) hA]
  congr 1

/-- The state component after `samples` accumulator updates is the ordinary
`samples`-step Markov marginal. -/
theorem markovSumLaw_map_fst
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) (mu : Measure S) : ∀ samples,
    (markovSumLaw P f samples mu).map Prod.fst = iterate P mu samples := by
  intro samples
  induction samples with
  | zero =>
      rw [markovSumLaw, Measure.map_map measurable_fst (by fun_prop)]
      simp [Function.comp_def]
  | succ samples ih =>
      rw [markovSumLaw_succ_eq_comp P f hf,
        Measure.map_comp _ _ measurable_fst]
      have hkernel : (markovSumKernel P f hf).map Prod.fst =
          P.comap Prod.fst measurable_fst := by
        ext stateSum A hA
        rw [Kernel.map_apply' _ measurable_fst _ hA,
          Kernel.comap_apply, markovSumKernel_apply]
        have hm : Measurable (fun next : S =>
            (next, stateSum.2 + f next)) := by fun_prop
        rw [Measure.map_apply hm (measurable_fst hA)]
        rfl
      rw [hkernel]
      calc
        P.comap Prod.fst measurable_fst ∘ₘ markovSumLaw P f samples mu =
            P ∘ₘ ((Kernel.deterministic Prod.fst measurable_fst) ∘ₘ
              markovSumLaw P f samples mu) := by
                rw [Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]
        _ = P ∘ₘ (markovSumLaw P f samples mu).map Prod.fst := by
              congr 1
              exact Measure.deterministic_comp_eq_map measurable_fst
        _ = P ∘ₘ iterate P mu samples := by rw [ih]
        _ = iterate P mu (samples + 1) := by rw [iterate_succ]; rfl

/-- A uniformly bounded observable gives a deterministic bound on the finite
accumulator.  This supplies all integrability facts needed below. -/
theorem markovSumLaw_ae_abs_snd_le
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) (mu : Measure S) : ∀ samples : ℕ,
    ∀ᵐ stateSum ∂markovSumLaw P f samples mu,
      |stateSum.2| ≤ (samples : ℝ) * B := by
  have habs : Measurable (fun stateSum : S × ℝ => |stateSum.2|) := by fun_prop
  intro samples
  induction samples with
  | zero =>
      rw [markovSumLaw]
      apply (ae_map_iff (by fun_prop)
        (measurableSet_le habs measurable_const)).2
      filter_upwards with x
      simp [hB]
  | succ samples ih =>
      rw [markovSumLaw_succ_eq_comp P f hf]
      apply Measure.ae_comp_of_ae_ae
        (measurableSet_le habs measurable_const)
      filter_upwards [ih] with stateSum hsum
      rw [markovSumKernel_apply]
      have hm : Measurable (fun next : S =>
          (next, stateSum.2 + f next)) := by fun_prop
      apply (ae_map_iff hm.aemeasurable
        (measurableSet_le habs measurable_const)).2
      filter_upwards with next
      calc
        |stateSum.2 + f next| ≤ |stateSum.2| + |f next| := abs_add_le _ _
        _ ≤ (samples : ℝ) * B + B := add_le_add hsum (hbound next)
        _ = (samples + 1 : ℕ) * B := by push_cast; ring

theorem integrable_snd_mul_fst_markovSumLaw
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) (mu : Measure S)
    [IsProbabilityMeasure mu] {g : S → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : 0 ≤ C) (hgbound : ∀ x, |g x| ≤ C)
    (samples : ℕ) :
    Integrable (fun stateSum => stateSum.2 * g stateSum.1)
      (markovSumLaw P f samples mu) := by
  let _ : IsProbabilityMeasure (markovSumLaw P f samples mu) :=
    markovSumLaw_isProbabilityMeasure P hf mu samples
  apply Integrable.of_bound (by fun_prop) ((samples : ℝ) * B * C)
  filter_upwards [markovSumLaw_ae_abs_snd_le P hf hB hbound mu samples]
    with stateSum hsum
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hsum (hgbound stateSum.1) (abs_nonneg _) (mul_nonneg (by positivity) hB)

theorem markovSumLaw_map_fst_of_invariant
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) {pi : Measure S} (hinv : Kernel.Invariant P pi)
    (samples : ℕ) :
    (markovSumLaw P f samples pi).map Prod.fst = pi := by
  rw [markovSumLaw_map_fst P hf pi samples, iterate_invariant hinv]

theorem integral_fst_markovSumLaw_of_invariant
    (P : Kernel S S) [IsMarkovKernel P] {f h : S → ℝ}
    (hf : Measurable f) (hh : Measurable h) {pi : Measure S}
    (hinv : Kernel.Invariant P pi) (samples : ℕ) :
    (∫ stateSum, h stateSum.1 ∂markovSumLaw P f samples pi) =
      ∫ x, h x ∂pi := by
  calc
    (∫ stateSum, h stateSum.1 ∂markovSumLaw P f samples pi) =
        ∫ x, h x ∂(markovSumLaw P f samples pi).map Prod.fst :=
      (integral_map measurable_fst.aemeasurable hh.aestronglyMeasurable).symm
    _ = ∫ x, h x ∂pi := by
      rw [markovSumLaw_map_fst_of_invariant P hf hinv samples]

theorem abs_markovOp_le_of_abs_le
    (P : Kernel S S) [IsMarkovKernel P] {g : S → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, |g x| ≤ C) (x : S) :
    |markovOp P g x| ≤ C := by
  let _ : IsProbabilityMeasure (P x) := IsMarkovKernel.isProbabilityMeasure x
  have hgint : Integrable g (P x) :=
    Integrable.of_bound hg.aestronglyMeasurable C <|
      ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hbound y
  unfold markovOp
  calc
    |∫ y, g y ∂P x| ≤ ∫ y, |g y| ∂P x := abs_integral_le_integral_abs
    _ ≤ ∫ _y, C ∂P x := integral_mono hgint.abs (integrable_const C) hbound
    _ = C := by simp

theorem integral_markovSumKernel_snd_mul
    (P : Kernel S S) [IsMarkovKernel P] {f g : S → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hfbound : ∀ x, |f x| ≤ B)
    (hgbound : ∀ x, |g x| ≤ C) (stateSum : S × ℝ) :
    (∫ nextSum, nextSum.2 * g nextSum.1
      ∂markovSumKernel P f hf stateSum) =
      stateSum.2 * markovOp P g stateSum.1 +
        markovOp P (fun y => f y * g y) stateSum.1 := by
  let _ : IsProbabilityMeasure (P stateSum.1) :=
    IsMarkovKernel.isProbabilityMeasure stateSum.1
  have hgint : Integrable g (P stateSum.1) :=
    Integrable.of_bound hg.aestronglyMeasurable C <|
      ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hgbound y
  have hfgint : Integrable (fun y => f y * g y) (P stateSum.1) := by
    apply hgint.bdd_mul (hf.aestronglyMeasurable)
    exact ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hfbound y
  rw [markovSumKernel_apply]
  have hm : Measurable (fun next : S =>
      (next, stateSum.2 + f next)) := by fun_prop
  rw [integral_map hm.aemeasurable (by fun_prop)]
  have hfun : (fun next : S => (stateSum.2 + f next) * g next) =
      fun next => stateSum.2 * g next + f next * g next := by
    funext next
    ring
  rw [hfun, integral_add (hgint.const_mul _) hfgint, integral_const_mul]
  rfl

/-- Initial-law domination is preserved by the complete finite dependent
sampling experiment. -/
theorem markovSumLaw_le_smul_of_le_smul
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) {mu pi : Measure S}
    {M : ENNReal} (h : mu ≤ M • pi) : ∀ samples,
    markovSumLaw P f samples mu ≤ M • markovSumLaw P f samples pi := by
  intro samples
  induction samples with
  | zero =>
      exact (Measure.map_mono_of_aemeasurable h (by fun_prop)).trans_eq
        (Measure.map_smul _ _ _)
  | succ samples ih =>
      simp only [markovSumLaw]
      let Q : S × ℝ → Measure (S × ℝ) := fun stateSum =>
        (P stateSum.1).map fun next => (next, stateSum.2 + f next)
      have hQ : Measurable Q := measurable_markovSumStep P hf
      calc
        (markovSumLaw P f samples mu).bind Q ≤
            (M • markovSumLaw P f samples pi).bind Q :=
          ArlibCommunity.Algorithms.CV18.measure_bind_mono_left ih hQ
        _ = M • (markovSumLaw P f samples pi).bind Q := by
          rw [Measure.bind_smul]

/-- Warmness therefore controls every failure event of the complete dependent
finite sampling experiment. -/
theorem markovSumLaw_le_smul_of_isWarm
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) {mu pi : Measure S}
    {M : ENNReal} (h : Arlib.IsWarm M mu pi) (samples : ℕ) :
    markovSumLaw P f samples mu ≤ M • markovSumLaw P f samples pi :=
  markovSumLaw_le_smul_of_le_smul P hf
    ((isWarm_iff_le_smul _ _).1 h) samples

/-- Real-valued Cauchy--Schwarz in the form used for Markov correlations. -/
theorem integral_mul_le_sqrt_mul_sqrt {pi : Measure S}
    {f g : S → ℝ} (hf : MemLp f 2 pi) (hg : MemLp g 2 pi) :
    (∫ x, f x * g x ∂pi) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂pi) *
        Real.sqrt (∫ x, g x ^ 2 ∂pi) := by
  have hprod : Integrable (fun x => f x * g x) pi := hf.integrable_mul hg
  have habsprod : Integrable (fun x => ‖f x‖ * ‖g x‖) pi :=
    hf.norm.integrable_mul hg.norm
  have hf' : MemLp f (ENNReal.ofReal 2) pi := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) pi := by simpa using hg
  calc
    (∫ x, f x * g x ∂pi) ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂pi := by
      apply integral_mono_ae hprod habsprod
      filter_upwards with x
      simpa [Real.norm_eq_abs, abs_mul] using le_abs_self (f x * g x)
    _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂pi) ^ (1 / 2 : ℝ) *
          (∫ x, ‖g x‖ ^ (2 : ℝ) ∂pi) ^ (1 / 2 : ℝ) :=
      integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
    _ = Real.sqrt (∫ x, f x ^ 2 ∂pi) *
          Real.sqrt (∫ x, g x ^ 2 ∂pi) := by
      simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-- Correlations of a centered observable decay at the `L²` mixing rate.
This is the dependent-sample estimate used in the variance calculation for
CV18's empirical ratio and covariance estimators. -/
theorem integral_mul_markovIter_le
    {P : Kernel S S} [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi) {f : S → ℝ}
    (hf : Measurable f) (hmem : MemLp f 2 pi)
    (hmean : ∫ x, f x ∂pi = 0) (t : ℕ) :
    (∫ x, f x * markovIter P f t x ∂pi) ≤
      |1 - spectralGap P pi| ^ t * varianceReal pi f := by
  have hTmem : MemLp (markovIter P f t) 2 pi :=
    memLp_markovIter hrev.invariant hf hmem t
  have hTmean : ∫ x, markovIter P f t x ∂pi = 0 := by
    rw [integral_markovIter hrev hf hmem t, hmean]
  have hfsq : ∫ x, f x ^ 2 ∂pi = varianceReal pi f := by
    rw [varianceReal_eq_sub hmem, hmean]
    ring
  have hTsq : ∫ x, markovIter P f t x ^ 2 ∂pi =
      varianceReal pi (markovIter P f t) := by
    rw [varianceReal_eq_sub hTmem, hTmean]
    ring
  have hv := varianceReal_markovIter_le hrev hpsd hf hmem t
  calc
    (∫ x, f x * markovIter P f t x ∂pi)
        ≤ Real.sqrt (∫ x, f x ^ 2 ∂pi) *
            Real.sqrt (∫ x, markovIter P f t x ^ 2 ∂pi) :=
          integral_mul_le_sqrt_mul_sqrt hmem hTmem
    _ = Real.sqrt (varianceReal pi f) *
          Real.sqrt (varianceReal pi (markovIter P f t)) := by rw [hfsq, hTsq]
    _ ≤ Real.sqrt (varianceReal pi f) *
          Real.sqrt ((((1 - spectralGap P pi) ^ 2) ^ t) * varianceReal pi f) := by
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _)
    _ = Real.sqrt (varianceReal pi f) *
          (|1 - spectralGap P pi| ^ t * Real.sqrt (varianceReal pi f)) := by
          congr 1
          rw [Real.sqrt_mul (by positivity), ← pow_mul, Nat.mul_comm 2 t,
            pow_mul, Real.sqrt_sq_eq_abs, abs_pow]
    _ = |1 - spectralGap P pi| ^ t * varianceReal pi f := by
          calc
            Real.sqrt (varianceReal pi f) *
                (|1 - spectralGap P pi| ^ t * Real.sqrt (varianceReal pi f)) =
                |1 - spectralGap P pi| ^ t *
                  (Real.sqrt (varianceReal pi f) * Real.sqrt (varianceReal pi f)) := by ring
            _ = |1 - spectralGap P pi| ^ t * varianceReal pi f := by
              rw [Real.mul_self_sqrt (varianceReal_nonneg pi f)]

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.markovSumLaw_le_smul_of_isWarm
#print axioms Arlib.MarkovChains.markovSumLaw_isProbabilityMeasure
#print axioms Arlib.MarkovChains.integral_mul_le_sqrt_mul_sqrt
#print axioms Arlib.MarkovChains.integral_mul_markovIter_le
