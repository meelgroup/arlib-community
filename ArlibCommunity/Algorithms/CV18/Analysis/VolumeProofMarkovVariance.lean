/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMarkovEmpirical

/-! # Stationary variance of finite Markov averages -/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory

variable {S : Type*} [MeasurableSpace S]

/-- The elementary one-step cross-moment identity, before averaging over the
law of the current state and accumulated sum. -/
theorem integral_add_mul_markovOp
    (P : Kernel S S) [IsMarkovKernel P] {f g : S → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hfbound : ∀ x, |f x| ≤ B)
    (hgbound : ∀ x, |g x| ≤ C) (stateSum : S × ℝ) :
    (∫ next, (stateSum.2 + f next) * g next ∂P stateSum.1) =
      stateSum.2 * markovOp P g stateSum.1 +
        markovOp P (fun y => f y * g y) stateSum.1 := by
  let _ : IsProbabilityMeasure (P stateSum.1) :=
    IsMarkovKernel.isProbabilityMeasure stateSum.1
  have hgint : Integrable g (P stateSum.1) :=
    Integrable.of_bound hg.aestronglyMeasurable C <|
      ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hgbound y
  have hfgint : Integrable (fun y => f y * g y) (P stateSum.1) := by
    apply hgint.bdd_mul hf.aestronglyMeasurable
    exact ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hfbound y
  have hfun : (fun next : S => (stateSum.2 + f next) * g next) =
      fun next => stateSum.2 * g next + f next * g next := by
    funext next
    ring
  rw [hfun, integral_add (hgint.const_mul _) hfgint, integral_const_mul]
  rfl

/-- Bounded observables make the joint current/next-state cross moment
integrable. This is the Fubini side condition for the dependent recurrence. -/
theorem integrable_markovSum_compProd_add_mul
    (P : Kernel S S) [IsMarkovKernel P] {f g : S → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfbound : ∀ x, |f x| ≤ B) (hgbound : ∀ x, |g x| ≤ C)
    (samples : ℕ) (mu : Measure S) [IsProbabilityMeasure mu] :
    Integrable (fun p : (S × ℝ) × S =>
      (p.1.2 + f p.2) * g p.2)
      ((markovSumLaw P f samples mu) ⊗ₘ
        (P.comap Prod.fst measurable_fst)) := by
  let _ : IsProbabilityMeasure (markovSumLaw P f samples mu) :=
    markovSumLaw_isProbabilityMeasure P hf mu samples
  apply Integrable.of_bound (by fun_prop) (((samples : ℝ) * B + B) * C)
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_le (by fun_prop) (by fun_prop))
  filter_upwards [markovSumLaw_ae_abs_snd_le P hf hB hfbound mu samples]
    with stateSum hsum
  filter_upwards with next
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |stateSum.2 + f next| * |g next| ≤
        (|stateSum.2| + |f next|) * |g next| :=
      mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
    _ ≤ (((samples : ℝ) * B) + B) * C :=
      mul_le_mul (add_le_add hsum (hfbound next)) (hgbound next)
        (abs_nonneg _) (add_nonneg (mul_nonneg (by positivity) hB) hB)

theorem integral_markovSumLaw_succ_eq_integral_compProd
    (P : Kernel S S) [IsMarkovKernel P] {f g : S → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (samples : ℕ) (mu : Measure S) [IsProbabilityMeasure mu]
    (hjoint : Integrable
      (fun p : (S × ℝ) × S => (p.1.2 + f p.2) * g p.2)
      ((markovSumLaw P f samples mu) ⊗ₘ
        (P.comap Prod.fst measurable_fst))) :
    (∫ stateSum, stateSum.2 * g stateSum.1
        ∂markovSumLaw P f (samples + 1) mu) =
      ∫ stateSum, ∫ next,
        (stateSum.2 + f next) * g next ∂P stateSum.1
        ∂markovSumLaw P f samples mu := by
  let _ : IsProbabilityMeasure (markovSumLaw P f samples mu) :=
    markovSumLaw_isProbabilityMeasure P hf mu samples
  rw [markovSumLaw_succ_eq_map_compProd P f hf]
  have htransform : Measurable (fun p : (S × ℝ) × S =>
      (p.2, p.1.2 + f p.2)) := by fun_prop
  rw [integral_map htransform.aemeasurable (by fun_prop)]
  change (∫ p : (S × ℝ) × S, (p.1.2 + f p.2) * g p.2
      ∂((markovSumLaw P f samples mu) ⊗ₘ
        (P.comap Prod.fst measurable_fst))) = _
  rw [Measure.integral_compProd hjoint]
  congr with stateSum

/-- Stationary one-step recurrence for the cross moment between the running
sum and an observable of the current state. -/
theorem integral_markovSumLaw_succ_mul_eq
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {f g : S → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfbound : ∀ x, |f x| ≤ B) (hgbound : ∀ x, |g x| ≤ C)
    (samples : ℕ) :
    (∫ stateSum, stateSum.2 * g stateSum.1
        ∂markovSumLaw P f (samples + 1) pi) =
      (∫ stateSum, stateSum.2 * markovOp P g stateSum.1
        ∂markovSumLaw P f samples pi) +
      ∫ x, f x * g x ∂pi := by
  have hfgmeas : Measurable (fun x => f x * g x) := hf.mul hg
  have hfgbound : ∀ x, |f x * g x| ≤ B * C := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hfbound x) (hgbound x) (abs_nonneg _ ) hB
  have hTgbound : ∀ x, |markovOp P g x| ≤ C :=
    abs_markovOp_le_of_abs_le P hg hC hgbound
  have hcross : Integrable
      (fun stateSum => stateSum.2 * markovOp P g stateSum.1)
      (markovSumLaw P f samples pi) :=
    integrable_snd_mul_fst_markovSumLaw P hf hB hfbound pi
      (measurable_markovOp P hg) hC hTgbound samples
  let _ : IsProbabilityMeasure (markovSumLaw P f samples pi) :=
    markovSumLaw_isProbabilityMeasure P hf pi samples
  have hlast : Integrable
      (fun stateSum => markovOp P (fun x => f x * g x) stateSum.1)
      (markovSumLaw P f samples pi) := by
    apply Integrable.of_bound
      ((measurable_markovOp P hfgmeas).comp measurable_fst).aestronglyMeasurable
      (B * C)
    exact ae_of_all _ fun stateSum => by
      simpa [Real.norm_eq_abs] using
        abs_markovOp_le_of_abs_le P hfgmeas (mul_nonneg hB hC)
          hfgbound stateSum.1
  have hfgint : Integrable (fun x => f x * g x) pi := by
    apply Integrable.of_bound hfgmeas.aestronglyMeasurable (B * C)
    exact ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hfgbound x
  calc
    (∫ stateSum, stateSum.2 * g stateSum.1
        ∂markovSumLaw P f (samples + 1) pi) =
        ∫ stateSum, ∫ next, (stateSum.2 + f next) * g next
          ∂P stateSum.1 ∂markovSumLaw P f samples pi :=
      integral_markovSumLaw_succ_eq_integral_compProd P hf hg samples pi
        (integrable_markovSum_compProd_add_mul P hf hg hB hC
          hfbound hgbound samples pi)
    _ = ∫ stateSum,
          (stateSum.2 * markovOp P g stateSum.1 +
            markovOp P (fun x => f x * g x) stateSum.1)
          ∂markovSumLaw P f samples pi := by
      congr with stateSum
      exact integral_add_mul_markovOp P hf hg hfbound hgbound stateSum
    _ = (∫ stateSum, stateSum.2 * markovOp P g stateSum.1
          ∂markovSumLaw P f samples pi) +
        ∫ stateSum, markovOp P (fun x => f x * g x) stateSum.1
          ∂markovSumLaw P f samples pi := integral_add hcross hlast
    _ = (∫ stateSum, stateSum.2 * markovOp P g stateSum.1
          ∂markovSumLaw P f samples pi) +
        ∫ x, markovOp P (fun y => f y * g y) x ∂pi := by
      rw [integral_fst_markovSumLaw_of_invariant P hf
        (measurable_markovOp P hfgmeas) hrev.invariant samples]
    _ = (∫ stateSum, stateSum.2 * markovOp P g stateSum.1
          ∂markovSumLaw P f samples pi) +
        ∫ x, f x * g x ∂pi := by
      rw [integral_markovOp hrev hfgmeas hfgint]

/-- Iterating after one Markov step shifts the iteration index by one. -/
theorem markovIter_markovOp (P : Kernel S S) [IsMarkovKernel P]
    (g : S → ℝ) (t : ℕ) :
    markovIter P (markovOp P g) t = markovIter P g (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change markovOp P (markovIter P (markovOp P g) t) =
        markovOp P (markovIter P g (t + 1))
      rw [ih]

/-- Exact stationary cross-moment formula for a finite dependent Markov path.
It replaces the invalid shortcut of treating successive CV18 samples as
independent. -/
theorem integral_markovSumLaw_mul_eq_sum_correlations
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {f g : S → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfbound : ∀ x, |f x| ≤ B) (hgbound : ∀ x, |g x| ≤ C) :
    ∀ samples : ℕ,
    (∫ stateSum, stateSum.2 * g stateSum.1
        ∂markovSumLaw P f samples pi) =
      ∑ t ∈ Finset.range samples,
        ∫ x, f x * markovIter P g t x ∂pi := by
  intro samples
  induction samples generalizing g C with
  | zero =>
      simp only [markovSumLaw, Finset.range_zero, Finset.sum_empty]
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp
  | succ samples ih =>
      have hTgmeas : Measurable (markovOp P g) := measurable_markovOp P hg
      have hTgbound : ∀ x, |markovOp P g x| ≤ C :=
        abs_markovOp_le_of_abs_le P hg hC hgbound
      rw [integral_markovSumLaw_succ_mul_eq P hrev hf hg hB hC
        hfbound hgbound samples]
      rw [ih hTgmeas hC hTgbound]
      simp_rw [markovIter_markovOp]
      rw [Finset.sum_range_succ']
      simp only [markovIter_zero]

/-- The conditional second moment of one accumulator step. -/
theorem integral_add_sq_markovOp
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) {B : ℝ} (hfbound : ∀ x, |f x| ≤ B)
    (stateSum : S × ℝ) :
    (∫ next, (stateSum.2 + f next) ^ 2 ∂P stateSum.1) =
      stateSum.2 ^ 2 + 2 * stateSum.2 * markovOp P f stateSum.1 +
        markovOp P (fun y => f y ^ 2) stateSum.1 := by
  let _ : IsProbabilityMeasure (P stateSum.1) :=
    IsMarkovKernel.isProbabilityMeasure stateSum.1
  have hfint : Integrable f (P stateSum.1) :=
    Integrable.of_bound hf.aestronglyMeasurable B <|
      ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hfbound y
  have hfsqint : Integrable (fun y => f y ^ 2) (P stateSum.1) := by
    apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (B ^ 2)
    exact ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_sq]
      rw [sq_le_sq, abs_of_nonneg ((abs_nonneg _).trans (hfbound y))]
      exact hfbound y
  have hfun : (fun next : S => (stateSum.2 + f next) ^ 2) =
      fun next => stateSum.2 ^ 2 +
        (2 * stateSum.2) * f next + f next ^ 2 := by
    funext next
    ring
  have huniv : (P stateSum.1).real Set.univ = 1 := by
    simp [Measure.real]
  rw [hfun]
  calc
    (∫ next, (stateSum.2 ^ 2 + (2 * stateSum.2) * f next) + f next ^ 2
        ∂P stateSum.1) =
        (∫ next, stateSum.2 ^ 2 + (2 * stateSum.2) * f next
          ∂P stateSum.1) + ∫ next, f next ^ 2 ∂P stateSum.1 :=
      integral_add
        ((integrable_const (stateSum.2 ^ 2)).add (hfint.const_mul _)) hfsqint
    _ = ((∫ _next, stateSum.2 ^ 2 ∂P stateSum.1) +
          ∫ next, (2 * stateSum.2) * f next ∂P stateSum.1) +
          ∫ next, f next ^ 2 ∂P stateSum.1 := by
      rw [integral_add (integrable_const _) (hfint.const_mul _)]
    _ = stateSum.2 ^ 2 + 2 * stateSum.2 * markovOp P f stateSum.1 +
          markovOp P (fun y => f y ^ 2) stateSum.1 := by
      rw [integral_const, integral_const_mul, huniv]
      simp only [markovOp]
      ring

/-- The square of the next accumulator is integrable under the joint
current/next-state law. -/
theorem integrable_markovSum_compProd_add_sq
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hfbound : ∀ x, |f x| ≤ B)
    (samples : ℕ) (mu : Measure S) [IsProbabilityMeasure mu] :
    Integrable (fun p : (S × ℝ) × S => (p.1.2 + f p.2) ^ 2)
      ((markovSumLaw P f samples mu) ⊗ₘ
        (P.comap Prod.fst measurable_fst)) := by
  let _ : IsProbabilityMeasure (markovSumLaw P f samples mu) :=
    markovSumLaw_isProbabilityMeasure P hf mu samples
  apply Integrable.of_bound (by fun_prop) (((samples : ℝ) * B + B) ^ 2)
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_le (by fun_prop) (by fun_prop))
  filter_upwards [markovSumLaw_ae_abs_snd_le P hf hB hfbound mu samples]
    with stateSum hsum
  filter_upwards with next
  rw [Real.norm_eq_abs, abs_sq]
  rw [sq_le_sq, abs_of_nonneg
    (add_nonneg (mul_nonneg (by positivity) hB) hB)]
  exact (abs_add_le _ _).trans (add_le_add hsum (hfbound next))

/-- Fubini expansion of the next accumulator's second moment. -/
theorem integral_markovSumLaw_succ_sq_eq
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hfbound : ∀ x, |f x| ≤ B)
    (samples : ℕ) (mu : Measure S) [IsProbabilityMeasure mu] :
    (∫ stateSum, stateSum.2 ^ 2
        ∂markovSumLaw P f (samples + 1) mu) =
      ∫ stateSum, ∫ next, (stateSum.2 + f next) ^ 2
        ∂P stateSum.1 ∂markovSumLaw P f samples mu := by
  let _ : IsProbabilityMeasure (markovSumLaw P f samples mu) :=
    markovSumLaw_isProbabilityMeasure P hf mu samples
  rw [markovSumLaw_succ_eq_map_compProd P f hf]
  have htransform : Measurable (fun p : (S × ℝ) × S =>
      (p.2, p.1.2 + f p.2)) := by fun_prop
  rw [integral_map htransform.aemeasurable (by fun_prop)]
  change (∫ p : (S × ℝ) × S, (p.1.2 + f p.2) ^ 2
      ∂((markovSumLaw P f samples mu) ⊗ₘ
        (P.comap Prod.fst measurable_fst))) = _
  rw [Measure.integral_compProd
    (integrable_markovSum_compProd_add_sq P hf hB hfbound samples mu)]
  congr with stateSum

/-- Stationary recurrence for the accumulator's second moment. -/
theorem integral_markovSumLaw_succ_sq_recurrence
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hfbound : ∀ x, |f x| ≤ B) (samples : ℕ) :
    (∫ stateSum, stateSum.2 ^ 2
        ∂markovSumLaw P f (samples + 1) pi) =
      (∫ stateSum, stateSum.2 ^ 2
        ∂markovSumLaw P f samples pi) +
      2 * (∫ stateSum, stateSum.2 * markovOp P f stateSum.1
        ∂markovSumLaw P f samples pi) +
      ∫ x, f x ^ 2 ∂pi := by
  have hfsqmeas : Measurable (fun x => f x ^ 2) := hf.pow_const 2
  have hfsqbound : ∀ x, |f x ^ 2| ≤ B ^ 2 := by
    intro x
    rw [abs_sq, sq_le_sq, abs_of_nonneg hB]
    exact hfbound x
  have hTfbound : ∀ x, |markovOp P f x| ≤ B :=
    abs_markovOp_le_of_abs_le P hf hB hfbound
  let _ : IsProbabilityMeasure (markovSumLaw P f samples pi) :=
    markovSumLaw_isProbabilityMeasure P hf pi samples
  have hsquare : Integrable (fun stateSum : S × ℝ => stateSum.2 ^ 2)
      (markovSumLaw P f samples pi) := by
    apply Integrable.of_bound (by fun_prop) (((samples : ℝ) * B) ^ 2)
    filter_upwards [markovSumLaw_ae_abs_snd_le P hf hB hfbound pi samples]
      with stateSum hsum
    rw [Real.norm_eq_abs, abs_sq, sq_le_sq,
      abs_of_nonneg (mul_nonneg (by positivity) hB)]
    exact hsum
  have hcross : Integrable
      (fun stateSum => stateSum.2 * markovOp P f stateSum.1)
      (markovSumLaw P f samples pi) :=
    integrable_snd_mul_fst_markovSumLaw P hf hB hfbound pi
      (measurable_markovOp P hf) hB hTfbound samples
  have hlast : Integrable
      (fun stateSum => markovOp P (fun x => f x ^ 2) stateSum.1)
      (markovSumLaw P f samples pi) := by
    apply Integrable.of_bound
      ((measurable_markovOp P hfsqmeas).comp measurable_fst).aestronglyMeasurable
      (B ^ 2)
    exact ae_of_all _ fun stateSum => by
      simpa [Real.norm_eq_abs] using
        abs_markovOp_le_of_abs_le P hfsqmeas (sq_nonneg B)
          hfsqbound stateSum.1
  have hfsqint : Integrable (fun x => f x ^ 2) pi := by
    apply Integrable.of_bound hfsqmeas.aestronglyMeasurable (B ^ 2)
    exact ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hfsqbound x
  have houterfun : (fun stateSum : S × ℝ =>
      stateSum.2 ^ 2 + 2 * stateSum.2 * markovOp P f stateSum.1 +
        markovOp P (fun x => f x ^ 2) stateSum.1) =
      fun stateSum =>
        (stateSum.2 ^ 2 + 2 *
          (stateSum.2 * markovOp P f stateSum.1)) +
        markovOp P (fun x => f x ^ 2) stateSum.1 := by
    funext stateSum
    ring
  calc
    (∫ stateSum, stateSum.2 ^ 2
        ∂markovSumLaw P f (samples + 1) pi) =
      ∫ stateSum, ∫ next, (stateSum.2 + f next) ^ 2
        ∂P stateSum.1 ∂markovSumLaw P f samples pi :=
      integral_markovSumLaw_succ_sq_eq P hf hB hfbound samples pi
    _ = ∫ stateSum,
        (stateSum.2 ^ 2 + 2 * stateSum.2 * markovOp P f stateSum.1 +
          markovOp P (fun x => f x ^ 2) stateSum.1)
        ∂markovSumLaw P f samples pi := by
      congr with stateSum
      exact integral_add_sq_markovOp P hf hfbound stateSum
    _ = (∫ stateSum, stateSum.2 ^ 2
          ∂markovSumLaw P f samples pi) +
        2 * (∫ stateSum, stateSum.2 * markovOp P f stateSum.1
          ∂markovSumLaw P f samples pi) +
        ∫ stateSum, markovOp P (fun x => f x ^ 2) stateSum.1
          ∂markovSumLaw P f samples pi := by
      rw [houterfun]
      calc
        (∫ stateSum,
            (stateSum.2 ^ 2 + 2 *
              (stateSum.2 * markovOp P f stateSum.1)) +
              markovOp P (fun x => f x ^ 2) stateSum.1
            ∂markovSumLaw P f samples pi) =
            (∫ stateSum, stateSum.2 ^ 2 + 2 *
              (stateSum.2 * markovOp P f stateSum.1)
              ∂markovSumLaw P f samples pi) +
            ∫ stateSum, markovOp P (fun x => f x ^ 2) stateSum.1
              ∂markovSumLaw P f samples pi :=
          integral_add (hsquare.add (hcross.const_mul 2)) hlast
        _ = ((∫ stateSum, stateSum.2 ^ 2
              ∂markovSumLaw P f samples pi) +
            ∫ stateSum, 2 *
              (stateSum.2 * markovOp P f stateSum.1)
              ∂markovSumLaw P f samples pi) +
            ∫ stateSum, markovOp P (fun x => f x ^ 2) stateSum.1
              ∂markovSumLaw P f samples pi := by
          rw [integral_add hsquare (hcross.const_mul 2)]
        _ = _ := by rw [integral_const_mul]
    _ = (∫ stateSum, stateSum.2 ^ 2
          ∂markovSumLaw P f samples pi) +
        2 * (∫ stateSum, stateSum.2 * markovOp P f stateSum.1
          ∂markovSumLaw P f samples pi) +
        ∫ x, markovOp P (fun y => f y ^ 2) x ∂pi := by
      rw [integral_fst_markovSumLaw_of_invariant P hf
        (measurable_markovOp P hfsqmeas) hrev.invariant samples]
    _ = (∫ stateSum, stateSum.2 ^ 2
          ∂markovSumLaw P f samples pi) +
        2 * (∫ stateSum, stateSum.2 * markovOp P f stateSum.1
          ∂markovSumLaw P f samples pi) +
        ∫ x, f x ^ 2 ∂pi := by
      rw [integral_markovOp hrev hfsqmeas hfsqint]

/-- A finite nonnegative geometric sum is bounded by its infinite sum. -/
theorem sum_range_pow_le_inv_one_sub {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (samples : ℕ) :
    (∑ t ∈ Finset.range samples, r ^ t) ≤ (1 - r)⁻¹ := by
  have hnonneg : ∀ t : ℕ, 0 ≤ r ^ t := fun t => pow_nonneg hr t
  convert! (summable_geometric_of_lt_one hr hr1).sum_le_tsum
    (Finset.range samples) (fun t _ => hnonneg t)
  exact (tsum_geometric_of_lt_one hr hr1).symm

/-- The running-sum/next-observable cross moment is controlled by inverse
spectral gap. -/
theorem integral_markovSumLaw_mul_markovOp_le_inv_gap
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty)
    {f : S → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi)
    (hmean : ∫ x, f x ∂pi = 0)
    {B : ℝ} (hB : 0 ≤ B) (hfbound : ∀ x, |f x| ≤ B)
    (hgap : 0 < spectralGap P pi) (samples : ℕ) :
    (∫ stateSum, stateSum.2 * markovOp P f stateSum.1
        ∂markovSumLaw P f samples pi) ≤
      (spectralGap P pi)⁻¹ * varianceReal pi f := by
  have hgap1 : spectralGap P pi ≤ 1 := spectralGap_le_one hrev hpsd hne
  have hr0 : 0 ≤ 1 - spectralGap P pi := by linarith
  have hr1 : 1 - spectralGap P pi < 1 := by linarith
  have hTfbound : ∀ x, |markovOp P f x| ≤ B :=
    abs_markovOp_le_of_abs_le P hf hB hfbound
  rw [integral_markovSumLaw_mul_eq_sum_correlations P hrev hf
    (measurable_markovOp P hf) hB hB hfbound hTfbound samples]
  simp_rw [markovIter_markovOp]
  calc
    (∑ t ∈ Finset.range samples,
        ∫ x, f x * markovIter P f (t + 1) x ∂pi) ≤
        ∑ t ∈ Finset.range samples,
          (1 - spectralGap P pi) ^ (t + 1) * varianceReal pi f := by
      apply Finset.sum_le_sum
      intro t ht
      simpa [abs_of_nonneg hr0] using
        integral_mul_markovIter_le hrev hpsd hf hmem hmean (t + 1)
    _ = (∑ t ∈ Finset.range samples,
          (1 - spectralGap P pi) ^ (t + 1)) * varianceReal pi f := by
      rw [Finset.sum_mul]
    _ ≤ (∑ t ∈ Finset.range samples,
          (1 - spectralGap P pi) ^ t) * varianceReal pi f := by
      apply mul_le_mul_of_nonneg_right _ (varianceReal_nonneg pi f)
      apply Finset.sum_le_sum
      intro t ht
      rw [pow_succ]
      calc
        (1 - spectralGap P pi) ^ t * (1 - spectralGap P pi) ≤
            (1 - spectralGap P pi) ^ t * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hr0 t)
        _ = (1 - spectralGap P pi) ^ t := mul_one _
    _ ≤ (spectralGap P pi)⁻¹ * varianceReal pi f := by
      apply mul_le_mul_of_nonneg_right _ (varianceReal_nonneg pi f)
      have hgeo := sum_range_pow_le_inv_one_sub hr0 hr1 samples
      have heq : 1 - (1 - spectralGap P pi) = spectralGap P pi := by ring
      rw [heq] at hgeo
      exact hgeo

/-- Stationary second moment of a centered bounded Markov sum. The linear
growth in `samples`, rather than quadratic growth, is the quantitative
dependent-sampling estimate needed by CV18. -/
theorem integral_markovSumLaw_sq_le
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty)
    {f : S → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi)
    (hmean : ∫ x, f x ∂pi = 0)
    {B : ℝ} (hB : 0 ≤ B) (hfbound : ∀ x, |f x| ≤ B)
    (hgap : 0 < spectralGap P pi) (samples : ℕ) :
    (∫ stateSum, stateSum.2 ^ 2
        ∂markovSumLaw P f samples pi) ≤
      (samples : ℝ) *
        (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f)) := by
  have hgap1 : spectralGap P pi ≤ 1 := spectralGap_le_one hrev hpsd hne
  have hinv0 : 0 ≤ (spectralGap P pi)⁻¹ := inv_nonneg.mpr hgap.le
  have honeinv : 1 ≤ (spectralGap P pi)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hgap]
    simpa using hgap1
  have hvar0 : 0 ≤ varianceReal pi f := varianceReal_nonneg pi f
  have hvarle : varianceReal pi f ≤
      (spectralGap P pi)⁻¹ * varianceReal pi f := by
    calc
      varianceReal pi f = 1 * varianceReal pi f := by ring
      _ ≤ (spectralGap P pi)⁻¹ * varianceReal pi f :=
        mul_le_mul_of_nonneg_right honeinv hvar0
  have hfsq : ∫ x, f x ^ 2 ∂pi = varianceReal pi f := by
    rw [varianceReal_eq_sub hmem, hmean]
    ring
  induction samples with
  | zero =>
      simp only [markovSumLaw, Nat.cast_zero, zero_mul]
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp
  | succ samples ih =>
      have hcross := integral_markovSumLaw_mul_markovOp_le_inv_gap
        P hrev hpsd hne hf hmem hmean hB hfbound hgap samples
      rw [integral_markovSumLaw_succ_sq_recurrence P hrev hf hB
        hfbound samples, hfsq]
      calc
        (∫ stateSum, stateSum.2 ^ 2 ∂markovSumLaw P f samples pi) +
              2 * (∫ stateSum,
                stateSum.2 * markovOp P f stateSum.1
                ∂markovSumLaw P f samples pi) + varianceReal pi f ≤
            (samples : ℝ) *
                (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f)) +
              2 * ((spectralGap P pi)⁻¹ * varianceReal pi f) +
              varianceReal pi f := by
          exact add_le_add
            (add_le_add ih (mul_le_mul_of_nonneg_left hcross (by norm_num))) le_rfl
        _ ≤ (samples : ℝ) *
                (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f)) +
              3 * ((spectralGap P pi)⁻¹ * varianceReal pi f) := by
          linarith
        _ = ((samples + 1 : ℕ) : ℝ) *
              (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f)) := by
          push_cast
          ring

/-- A Markov operator, and hence every iterate, preserves the constant-one
observable pointwise. -/
theorem markovIter_one (P : Kernel S S) [IsMarkovKernel P]
    (t : ℕ) (x : S) : markovIter P (fun _ : S => 1) t x = 1 := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      rw [markovIter_succ]
      unfold markovOp
      simp_rw [ih]
      simp [Measure.real]

/-- A centered stationary observable has a centered finite accumulated sum. -/
theorem integral_snd_markovSumLaw_eq_zero
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {f : S → ℝ} (hf : Measurable f) (hmean : ∫ x, f x ∂pi = 0)
    {B : ℝ} (hB : 0 ≤ B) (hfbound : ∀ x, |f x| ≤ B)
    (samples : ℕ) :
    ∫ stateSum, stateSum.2 ∂markovSumLaw P f samples pi = 0 := by
  have h := integral_markovSumLaw_mul_eq_sum_correlations
    (g := fun _ : S => (1 : ℝ)) (B := B) (C := 1)
    P hrev hf measurable_const hB (by norm_num) hfbound
      (fun _ => by norm_num) samples
  simp_rw [markovIter_one] at h
  simp [hmean] at h
  exact h

/-- Chebyshev bound for the complete finite dependent Markov experiment,
started at stationarity. -/
theorem markovSumLaw_meas_abs_snd_ge_le
    (P : Kernel S S) [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty)
    {f : S → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi)
    (hmean : ∫ x, f x ∂pi = 0)
    {B : ℝ} (hB : 0 ≤ B) (hfbound : ∀ x, |f x| ≤ B)
    (hgap : 0 < spectralGap P pi) (samples : ℕ)
    {c : ℝ} (hc : 0 < c) :
    markovSumLaw P f samples pi {stateSum | c ≤ |stateSum.2|} ≤
      ENNReal.ofReal (((samples : ℝ) *
        (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f))) / c ^ 2) := by
  let _ : IsProbabilityMeasure (markovSumLaw P f samples pi) :=
    markovSumLaw_isProbabilityMeasure P hf pi samples
  have hX : MemLp (fun stateSum : S × ℝ => stateSum.2) 2
      (markovSumLaw P f samples pi) := by
    apply MemLp.of_bound (by fun_prop) ((samples : ℝ) * B)
    filter_upwards [markovSumLaw_ae_abs_snd_le P hf hB hfbound pi samples]
      with stateSum hsum
    simpa [Real.norm_eq_abs] using hsum
  have hsumMean :
      ∫ stateSum, stateSum.2 ∂markovSumLaw P f samples pi = 0 :=
    integral_snd_markovSumLaw_eq_zero P hrev hf hmean hB hfbound samples
  have hvariance : variance (fun stateSum : S × ℝ => stateSum.2)
      (markovSumLaw P f samples pi) =
      ∫ stateSum, stateSum.2 ^ 2 ∂markovSumLaw P f samples pi := by
    rw [variance_eq_sub hX, hsumMean]
    simp only [Pi.pow_apply]
    ring
  have hcheb := meas_ge_le_variance_div_sq hX hc
  rw [hsumMean] at hcheb
  simp only [sub_zero] at hcheb
  refine hcheb.trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [hvariance]
  exact div_le_div_of_nonneg_right
    (integral_markovSumLaw_sq_le P hrev hpsd hne hf hmem hmean
      hB hfbound hgap samples) (sq_nonneg c)

/-- Warm-start version of the dependent Markov Chebyshev bound. Warmness is
paid once for the whole finite experiment, rather than once per sample. -/
theorem markovSumLaw_meas_abs_snd_ge_le_of_isWarm
    (P : Kernel S S) [IsMarkovKernel P] {mu pi : Measure S}
    [IsProbabilityMeasure pi]
    (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    (hne : (rayleighSet P pi).Nonempty)
    {f : S → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi)
    (hmean : ∫ x, f x ∂pi = 0)
    {B : ℝ} (hB : 0 ≤ B) (hfbound : ∀ x, |f x| ≤ B)
    (hgap : 0 < spectralGap P pi) {M : ENNReal}
    (hwarm : Arlib.IsWarm M mu pi) (samples : ℕ)
    {c : ℝ} (hc : 0 < c) :
    markovSumLaw P f samples mu {stateSum | c ≤ |stateSum.2|} ≤
      M * ENNReal.ofReal (((samples : ℝ) *
        (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f))) / c ^ 2) := by
  calc
    markovSumLaw P f samples mu {stateSum | c ≤ |stateSum.2|} ≤
        (M • markovSumLaw P f samples pi)
          {stateSum | c ≤ |stateSum.2|} :=
      markovSumLaw_le_smul_of_isWarm P hf hwarm samples
        {stateSum | c ≤ |stateSum.2|}
    _ = M * markovSumLaw P f samples pi
          {stateSum | c ≤ |stateSum.2|} := by
      rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ M * ENNReal.ofReal (((samples : ℝ) *
          (3 * ((spectralGap P pi)⁻¹ * varianceReal pi f))) / c ^ 2) := by
      gcongr
      exact markovSumLaw_meas_abs_snd_ge_le P hrev hpsd hne hf hmem
        hmean hB hfbound hgap samples hc

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.integral_markovSumLaw_mul_eq_sum_correlations
#print axioms Arlib.MarkovChains.integral_markovSumLaw_sq_le
#print axioms Arlib.MarkovChains.markovSumLaw_meas_abs_snd_ge_le
#print axioms Arlib.MarkovChains.markovSumLaw_meas_abs_snd_ge_le_of_isWarm
