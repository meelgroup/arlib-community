/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianResetL3Budget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceSlackMoments

/-!
# Product concentration on the chronological reset reference

This file is the reference-side counterpart of the scheduled reset coupling.
It allows the transported Lemma 7.17 coefficient to be as large as `5/2` of
the coefficient selected in Figure 1, and allows the equation-(6) phase
second moment to use one eighth of the executable slack.  The constants still
fit, without changing the `11/64` probability slot of Lemma 7.15.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-- The equation-(6) phase factor on the reset reference. -/
noncomputable def figureOneResetReferenceMomentFactor
    (q : VolumeParams) (j : ℕ) : ℝ :=
  figureOneChronologicalMomentFactor q j +
    figureOneExecutableMomentSlack q / 8

theorem figureOneResetReferenceMomentFactor_nonneg
    (q : VolumeParams) (j : ℕ) :
    0 ≤ figureOneResetReferenceMomentFactor q j := by
  unfold figureOneResetReferenceMomentFactor
  exact add_nonneg
    (zero_le_one.trans (figureOneChronologicalMomentFactor_one_le q j))
    (div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num))

theorem figureOneResetReferenceMomentFactor_le_executable
    (q : VolumeParams) (j : ℕ) :
    figureOneResetReferenceMomentFactor q j ≤
      figureOneExecutableMomentFactor q j := by
  let c := figureOneChronologicalMomentFactor q j
  let s := figureOneExecutableMomentSlack q
  have hc : 1 ≤ c := figureOneChronologicalMomentFactor_one_le q j
  have hs : 0 ≤ s := figureOneExecutableMomentSlack_nonneg q
  change c + s / 8 ≤ c * (1 + s)
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hs]

theorem figureOneResetReferenceMomentFactor_le_two
    (q : VolumeParams) (j : ℕ) :
    figureOneResetReferenceMomentFactor q j ≤ 2 :=
  (figureOneResetReferenceMomentFactor_le_executable q j).trans
    (figureOneExecutableMomentFactor_le_two q j)

/-- The reset factors, together with the outer Lemma 7.15 truncation, fit
the same `1 + eps²/32` normalized second-product budget as the executable
factors. -/
theorem figureOneResetReferenceMomentFactor_budget
    (q : VolumeParams) {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct (figureOneResetReferenceMomentFactor q) i *
        ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2 ≤
      1 + q.eps ^ 2 / 32 := by
  have hprod : dependentPhaseMeanProduct
      (figureOneResetReferenceMomentFactor q) i ≤
      dependentPhaseMeanProduct (figureOneExecutableMomentFactor q) i := by
    unfold dependentPhaseMeanProduct
    apply Finset.prod_le_prod
    · intro j hj
      exact figureOneResetReferenceMomentFactor_nonneg q (j + 1)
    · intro j hj
      exact figureOneResetReferenceMomentFactor_le_executable q (j + 1)
  have hpow : 0 ≤ ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2 :=
    sq_nonneg _
  exact (mul_le_mul_of_nonneg_right hprod hpow).trans
    (figureOneExecutableMomentFactor_budget q hi)

/-- The transported coefficient increases the Lemma 7.15 moment multiplier
from `eps²/2048` to at most `5 eps²/4096`. -/
theorem figureOneResetReference_momentMultiplier_le
    (q : VolumeParams) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ (5 / 2 : ℝ) * figureOneDependentEpsilon q)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    1 + 2 * epsilon * figureOneDependentAlpha q ^ 4 * i ≤
      1 + 5 * q.eps ^ 2 / 4096 := by
  have ha4 : 0 ≤ figureOneDependentAlpha q ^ 4 := by positivity
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hscale :
      2 * epsilon * figureOneDependentAlpha q ^ 4 * (i : ℝ) ≤
        (5 / 2 : ℝ) *
          (2 * figureOneDependentEpsilon q *
            figureOneDependentAlpha q ^ 4 * (i : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hepsilon
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha4) hi0)
    nlinarith
  have hbase := figureOneDependentMomentMultiplier_le q hi
  nlinarith

/-- The `5/2` transported coefficient and the reset equation-(6) budget
still leave the original `eps²/16` Chebyshev excess. -/
theorem figureOneResetReference_momentBudget_le (q : VolumeParams) :
    (1 + 5 * q.eps ^ 2 / 4096) * (1 + q.eps ^ 2 / 32) ≤
      1 + q.eps ^ 2 / 16 := by
  have hy0 : 0 ≤ q.eps ^ 2 := sq_nonneg q.eps
  have hy1 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]

/-- The transported coefficient retains the smallness premise in Lemma 7.15.
The large truncation parameter makes this substantially sharper than merely
scaling `figureOneDependent_smallness`. -/
theorem figureOneResetReference_smallness
    (q : VolumeParams) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ (5 / 2 : ℝ) * figureOneDependentEpsilon q) :
    4 * epsilon * figureOneDependentAlpha q ^ 3 ≤ 1 := by
  have ha := figureOneDependentAlpha_pos q
  have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  have ha1 : (1 : ℝ) ≤ figureOneDependentAlpha q :=
    figureOneDependentAlpha_one_le q
  have hm1 : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have hscaled : 4 * epsilon * figureOneDependentAlpha q ^ 3 ≤
      4 * ((5 / 2 : ℝ) * figureOneDependentEpsilon q) *
        figureOneDependentAlpha q ^ 3 := by
    gcongr
  rw [figureOneDependentEpsilon] at hscaled
  have hden : (0 : ℝ) <
      4096 * figureOneDependentAlpha q ^ 4 *
        figureOneDependentPhaseCount q := by positivity
  have htarget :
      4 * ((5 / 2 : ℝ) *
          (q.eps ^ 2 /
            (4096 * figureOneDependentAlpha q ^ 4 *
              figureOneDependentPhaseCount q))) *
          figureOneDependentAlpha q ^ 3 ≤ 1 := by
    rw [div_eq_mul_inv]
    field_simp [ha.ne', hm.ne']
    nlinarith [mul_le_mul ha1 hm1 zero_le_one ha.le]
  exact hscaled.trans htarget

/-- The recursive first-moment coefficient remains at most one after reset
transport. -/
theorem figureOneResetReference_coefficient
    (q : VolumeParams) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ (5 / 2 : ℝ) * figureOneDependentEpsilon q)
    {i : ℕ} (hi : i < figureOneDependentPhaseCount q) :
    2 * epsilon * figureOneDependentAlpha q ^ 2 * (i + 1) ≤ 1 := by
  have ha := figureOneDependentAlpha_pos q
  have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have hiNat : i + 1 ≤ figureOneDependentPhaseCount q := by omega
  have hiR : (i + 1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast hiNat
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  have ha2 : (1 : ℝ) ≤ figureOneDependentAlpha q ^ 2 :=
    one_le_pow₀ (figureOneDependentAlpha_one_le q)
  have hscaled :
      2 * epsilon * figureOneDependentAlpha q ^ 2 * (i + 1 : ℝ) ≤
        2 * ((5 / 2 : ℝ) * figureOneDependentEpsilon q) *
          figureOneDependentAlpha q ^ 2 * (i + 1 : ℝ) := by
    gcongr
  rw [figureOneDependentEpsilon] at hscaled
  have htarget :
      2 * ((5 / 2 : ℝ) *
          (q.eps ^ 2 /
            (4096 * figureOneDependentAlpha q ^ 4 *
              figureOneDependentPhaseCount q))) *
          figureOneDependentAlpha q ^ 2 * (i + 1 : ℝ) ≤ 1 := by
    rw [div_eq_mul_inv]
    field_simp [ha.ne', hm.ne']
    have hright : (i + 1 : ℝ) ≤
        figureOneDependentAlpha q ^ 2 *
          figureOneDependentPhaseCount q := by
      exact hiR.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ha2 hm.le)
    nlinarith
  exact hscaled.trans htarget

/-! ## Truncation of reset-reference coordinates -/

theorem figureOneChronologicalTruncatedSecond_le_of_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    {factor : ℕ → ℝ}
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      factor j * figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    figureOneChronologicalTruncatedSecond q I mu W j ≤
      factor j * figureOneChronologicalRawMean q I j ^ 2 := by
  have hVmem := figureOneChronologicalTruncatedPhase_memLp_two
    q I mu W hWmeas hW0 j
  have hle : figureOneChronologicalTruncatedSecond q I mu W j ≤
      ∫ omega, W j omega ^ 2 ∂mu := by
    apply integral_mono hVmem.integrable_sq (hWmem j).integrable_sq
    intro omega
    exact (sq_le_sq₀
      (figureOneChronologicalTruncatedPhase_nonneg q I W hW0 j omega)
      (hW0 j omega)).2
        (figureOneChronologicalTruncatedPhase_le q I W j omega)
  exact hle.trans (hWsecond j)

theorem figureOneChronologicalTruncatedMean_lower_of_two
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    (1 - 1 / (2 * figureOneDependentAlpha q)) *
        figureOneChronologicalRawMean q I j ≤
      figureOneChronologicalTruncatedMean q I mu W j := by
  let raw := figureOneChronologicalRawMean q I j
  let alpha := figureOneDependentAlpha q
  have hraw : 0 < raw := figureOneChronologicalRawMean_pos q I j
  have halpha : (1024 : ℝ) ≤ alpha := figureOneDependentAlpha_ge_1024 q
  have hcap : 0 < alpha * raw := mul_pos (by linarith) hraw
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    ((hWmem j).integrable (by norm_num)) (hWmem j).integrable_sq
      (hW0 j) hcap
  have hloss : (∫ omega, W j omega ^ 2 ∂mu) /
      (4 * (alpha * raw)) ≤ raw / (2 * alpha) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hcap)]
    field_simp [show alpha ≠ 0 by linarith]
    nlinarith [hWsecondTwo j]
  rw [hWmean j] at htrunc
  change (1 - 1 / (2 * alpha)) * raw ≤
    ∫ omega, min (W j omega) (alpha * raw) ∂mu
  calc
    _ = raw - raw / (2 * alpha) := by ring
    _ ≤ raw - (∫ omega, W j omega ^ 2 ∂mu) /
        (4 * (alpha * raw)) := sub_le_sub_left hloss raw
    _ ≤ _ := htrunc

theorem figureOneChronologicalRawMean_le_truncatedMean_of_two
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    figureOneChronologicalRawMean q I j ≤
      (1 + 1 / figureOneDependentAlpha q) *
        figureOneChronologicalTruncatedMean q I mu W j := by
  let raw := figureOneChronologicalRawMean q I j
  let alpha := figureOneDependentAlpha q
  have hraw : 0 < raw := figureOneChronologicalRawMean_pos q I j
  have halpha : (1024 : ℝ) ≤ alpha := figureOneDependentAlpha_ge_1024 q
  have hlower := figureOneChronologicalTruncatedMean_lower_of_two
    q I mu W hW0 hWmem hWmean hWsecondTwo j
  have hinv0 : 0 ≤ 1 / alpha := by positivity
  have hinv1 : 1 / alpha ≤ 1 :=
    (div_le_one (by linarith : 0 < alpha)).2 (by linarith)
  have hcoefficient : 1 ≤
      (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) := by
    rw [show (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) =
      1 + (1 / alpha) * (1 - 1 / alpha) / 2 by ring]
    nlinarith [mul_nonneg hinv0 (sub_nonneg.mpr hinv1)]
  have hscale := mul_le_mul_of_nonneg_left hlower
    (by positivity : 0 ≤ 1 + 1 / alpha)
  change raw ≤ (1 + 1 / alpha) *
    figureOneChronologicalTruncatedMean q I mu W j
  calc
    raw = 1 * raw := by ring
    _ ≤ ((1 + 1 / alpha) * (1 - 1 / (2 * alpha))) * raw :=
      mul_le_mul_of_nonneg_right hcoefficient hraw.le
    _ = (1 + 1 / alpha) * ((1 - 1 / (2 * alpha)) * raw) := by ring
    _ ≤ _ := hscale

theorem figureOneChronologicalTruncatedMean_pos_of_two
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    0 < figureOneChronologicalTruncatedMean q I mu W j := by
  have hlower := figureOneChronologicalTruncatedMean_lower_of_two
    q I mu W hW0 hWmem hWmean hWsecondTwo j
  have ha := figureOneDependentAlpha_ge_1024 q
  have hr := figureOneChronologicalRawMean_pos q I j
  have hap : 0 < figureOneDependentAlpha q := figureOneDependentAlpha_pos q
  have hinv : 1 / (2 * figureOneDependentAlpha q) ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hap)]
    nlinarith
  have hc : (3 / 4 : ℝ) ≤
      1 - 1 / (2 * figureOneDependentAlpha q) := by linarith
  exact (mul_pos (lt_of_lt_of_le (by norm_num) hc) hr).trans_le hlower

theorem figureOneChronologicalRawMean_le_two_truncatedMean_of_two
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    figureOneChronologicalRawMean q I j ≤
      2 * figureOneChronologicalTruncatedMean q I mu W j := by
  have hlower := figureOneChronologicalTruncatedMean_lower_of_two
    q I mu W hW0 hWmem hWmean hWsecondTwo j
  have ha := figureOneDependentAlpha_ge_1024 q
  have hr := figureOneChronologicalRawMean_pos q I j
  have hap : 0 < figureOneDependentAlpha q := figureOneDependentAlpha_pos q
  have hinv : 1 / (2 * figureOneDependentAlpha q) ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hap)]
    nlinarith
  have hc : (3 / 4 : ℝ) ≤
      1 - 1 / (2 * figureOneDependentAlpha q) := by linarith
  have h34 := (mul_le_mul_of_nonneg_right hc hr.le).trans hlower
  nlinarith

theorem figureOneChronologicalRawMean_sq_le_two_truncatedSecond_of_two
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    figureOneChronologicalRawMean q I j ^ 2 ≤
      2 * figureOneChronologicalTruncatedSecond q I mu W j := by
  have hlower := figureOneChronologicalTruncatedMean_lower_of_two
    q I mu W hW0 hWmem hWmean hWsecondTwo j
  have hm0 := (figureOneChronologicalTruncatedMean_pos_of_two
    q I mu W hW0 hWmem hWmean hWsecondTwo j).le
  have hr0 := (figureOneChronologicalRawMean_pos q I j).le
  have hap : 0 < figureOneDependentAlpha q := figureOneDependentAlpha_pos q
  have hinv : 1 / (2 * figureOneDependentAlpha q) ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hap)]
    nlinarith [figureOneDependentAlpha_ge_1024 q]
  have hc : (3 / 4 : ℝ) * figureOneChronologicalRawMean q I j ≤
      figureOneChronologicalTruncatedMean q I mu W j := by
    have hcoef : (3 / 4 : ℝ) ≤
        1 - 1 / (2 * figureOneDependentAlpha q) := by linarith
    exact (mul_le_mul_of_nonneg_right hcoef hr0).trans hlower
  have hsq : ((3 / 4 : ℝ) *
      figureOneChronologicalRawMean q I j) ^ 2 ≤
      figureOneChronologicalTruncatedMean q I mu W j ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) hr0) hm0).2 hc
  have hm2 := figureOneChronologicalTruncatedMean_sq_le_second
    q I mu W hWmeas hW0 j
  nlinarith [sq_nonneg (figureOneChronologicalRawMean q I j)]

theorem figureOneChronologicalRawMeanProduct_le_of_two
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * figureOneChronologicalRawMean q I j ^ 2) (i : ℕ) :
    dependentPhaseMeanProduct (figureOneChronologicalRawMean q I) i ≤
      (1 + 1 / figureOneDependentAlpha q) ^ i *
        dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedMean q I mu W) i := by
  unfold dependentPhaseMeanProduct
  calc
    (∏ j ∈ Finset.range i, figureOneChronologicalRawMean q I (j + 1)) ≤
        ∏ j ∈ Finset.range i,
          ((1 + 1 / figureOneDependentAlpha q) *
            figureOneChronologicalTruncatedMean q I mu W (j + 1)) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact (figureOneChronologicalRawMean_pos q I (j + 1)).le
      · intro j hj
        exact figureOneChronologicalRawMean_le_truncatedMean_of_two
          q I mu W hW0 hWmem hWmean hWsecondTwo (j + 1)
    _ = (1 + 1 / figureOneDependentAlpha q) ^ i *
        ∏ j ∈ Finset.range i,
          figureOneChronologicalTruncatedMean q I mu W (j + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

theorem figureOneChronologicalTruncatedSecondProduct_le_of_factor
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (factor : ℕ → ℝ)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      factor j * figureOneChronologicalRawMean q I j ^ 2) (i : ℕ) :
    dependentPhaseMeanProduct
        (figureOneChronologicalTruncatedSecond q I mu W) i ≤
      dependentPhaseMeanProduct factor i *
        dependentPhaseMeanProduct (figureOneChronologicalRawMean q I) i ^ 2 := by
  unfold dependentPhaseMeanProduct
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro j hj
    exact integral_nonneg fun _ => sq_nonneg _
  · intro j hj
    exact figureOneChronologicalTruncatedSecond_le_of_bound
      q I mu W hWmeas hW0 hWmem hWsecond (j + 1)

theorem figureOneChronologicalTruncatedSecondProduct_reset_normalized
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneResetReferenceMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct
        (figureOneChronologicalTruncatedSecond q I mu W) i ≤
      (1 + q.eps ^ 2 / 32) *
        dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedMean q I mu W) i ^ 2 := by
  let raw := dependentPhaseMeanProduct (figureOneChronologicalRawMean q I) i
  let truncated := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu W) i
  let factorProduct := dependentPhaseMeanProduct
    (figureOneResetReferenceMomentFactor q) i
  have hsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * figureOneChronologicalRawMean q I j ^ 2 := fun j =>
    (hWsecond j).trans (mul_le_mul_of_nonneg_right
      (figureOneResetReferenceMomentFactor_le_two q j) (sq_nonneg _))
  have hfactor0 : 0 ≤ factorProduct := dependentPhaseMeanProduct_nonneg _
    (figureOneResetReferenceMomentFactor_nonneg q) i
  have htruncated0 : 0 ≤ truncated := dependentPhaseMeanProduct_nonneg _
    (fun j => (figureOneChronologicalTruncatedMean_pos_of_two
      q I mu W hW0 hWmem hWmean hsecondTwo j).le) i
  have hraw0 : 0 ≤ raw := dependentPhaseMeanProduct_nonneg _
    (fun j => (figureOneChronologicalRawMean_pos q I j).le) i
  have hraw := figureOneChronologicalRawMeanProduct_le_of_two
    q I mu W hW0 hWmem hWmean hsecondTwo i
  have hcoef0 : 0 ≤ (1 + 1 / figureOneDependentAlpha q) ^ i := by
    apply pow_nonneg
    have ha := figureOneDependentAlpha_pos q
    positivity
  have hrawSq : raw ^ 2 ≤
      (((1 + 1 / figureOneDependentAlpha q) ^ i) * truncated) ^ 2 :=
    (sq_le_sq₀ hraw0 (mul_nonneg hcoef0 htruncated0)).2 hraw
  have hsecondProduct :=
    figureOneChronologicalTruncatedSecondProduct_le_of_factor
      q I mu W hWmeas hW0 hWmem
        (figureOneResetReferenceMomentFactor q) hWsecond i
  calc
    _ ≤ factorProduct * raw ^ 2 := hsecondProduct
    _ ≤ factorProduct *
        (((1 + 1 / figureOneDependentAlpha q) ^ i) * truncated) ^ 2 :=
      mul_le_mul_of_nonneg_left hrawSq hfactor0
    _ = (factorProduct *
          ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2) *
        truncated ^ 2 := by ring
    _ ≤ (1 + q.eps ^ 2 / 32) * truncated ^ 2 :=
      mul_le_mul_of_nonneg_right
        (figureOneResetReferenceMomentFactor_budget q hi) (sq_nonneg truncated)

theorem figureOneChronologicalTruncatedMeanProduct_relativeApprox_of_two
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * figureOneChronologicalRawMean q I j ^ 2) :
    RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (figureOneChronologicalTruncatedMean q I mu W)
        (figureOneDependentPhaseCount q)) := by
  rw [← figureOneChronologicalRawMean_product q I]
  let raw := dependentPhaseMeanProduct
    (figureOneChronologicalRawMean q I) (figureOneDependentPhaseCount q)
  let mean := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu W)
      (figureOneDependentPhaseCount q)
  have hrawPos : 0 < raw := by
    apply Finset.prod_pos
    intro j hj
    exact figureOneChronologicalRawMean_pos q I (j + 1)
  have hmean0 : 0 ≤ mean := dependentPhaseMeanProduct_nonneg _
    (fun j => integral_nonneg fun omega =>
      figureOneChronologicalTruncatedPhase_nonneg q I W hW0 j omega) _
  have hmeanRaw : mean ≤ raw :=
    figureOneChronologicalTruncatedMeanProduct_le_raw
      q I mu W hWmeas hW0 hWmem hWmean _
  have hrawPow := figureOneChronologicalRawMeanProduct_le_of_two
    q I mu W hW0 hWmem hWmean hWsecondTwo
      (figureOneDependentPhaseCount q)
  have hpow := figureOne_one_add_inv_alpha_pow_le_exp q (le_refl _)
  have hrawExp : raw ≤ Real.exp (q.eps ^ 2 / 1024) * mean :=
    hrawPow.trans (mul_le_mul_of_nonneg_right hpow hmean0)
  have hrawBound : raw ≤ (1 + q.eps ^ 2 / 512) * mean :=
    hrawExp.trans (mul_le_mul_of_nonneg_right
      (figureOne_exp_eps_sq_div_1024_le q) hmean0)
  have hcoef : (1 + q.eps ^ 2 / 512) * (1 - q.eps / 32) ≤ 1 := by
    nlinarith [mul_nonneg q.heps.1.le
      (sub_nonneg.mpr (by linarith [q.heps.2] : q.eps ≤ 32))]
  unfold RelativeApprox Arlib.relErr
  constructor
  · have hs : (1 + q.eps ^ 2 / 512) *
        ((1 - q.eps / 32) * raw) ≤
      (1 + q.eps ^ 2 / 512) * mean := by
      calc
        _ = ((1 + q.eps ^ 2 / 512) * (1 - q.eps / 32)) * raw := by ring
        _ ≤ raw := by simpa using mul_le_mul_of_nonneg_right hcoef hrawPos.le
        _ ≤ _ := hrawBound
    exact le_of_mul_le_mul_left hs (by positivity)
  · calc
      mean ≤ raw := hmeanRaw
      _ ≤ (1 + q.eps / 32) * raw := by
        nlinarith [hrawPos, q.heps.1]

theorem figureOneResetReference_relativeProduct_finite
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneResetReferenceMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ (5 / 2 : ℝ) * figureOneDependentEpsilon q) :
    ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * epsilon * figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (figureOneChronologicalTruncatedSecond q I mu W) i ≤
        2 * dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedMean q I mu W) i ^ 2 := by
  intro i hi
  let meanProduct := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu W) i
  have hm2 := figureOneChronologicalTruncatedSecondProduct_reset_normalized
    q I mu W hWmeas hW0 hWmem hWmean hWsecond hi
  have hmult := figureOneResetReference_momentMultiplier_le
    q hepsilon0 hepsilon hi
  have hmult0 : 0 ≤ 1 + 2 * epsilon *
      figureOneDependentAlpha q ^ 4 * (i : ℝ) := by positivity
  have htwo : 1 + q.eps ^ 2 / 16 ≤ (2 : ℝ) := by
    nlinarith [q.heps.1, q.heps.2]
  calc
    _ ≤ (1 + 2 * epsilon * figureOneDependentAlpha q ^ 4 * i) *
        ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
      mul_le_mul_of_nonneg_left hm2 hmult0
    _ ≤ ((1 + 5 * q.eps ^ 2 / 4096) *
          (1 + q.eps ^ 2 / 32)) * meanProduct ^ 2 := by
      have hs := mul_le_mul_of_nonneg_right hmult
        (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
      nlinarith
    _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right
        (figureOneResetReference_momentBudget_le q) (sq_nonneg meanProduct)
    _ ≤ 2 * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right htwo (sq_nonneg meanProduct)

theorem figureOneResetReference_tailSecond
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneResetReferenceMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ (5 / 2 : ℝ) * figureOneDependentEpsilon q) :
    (1 + 2 * epsilon * figureOneDependentAlpha q ^ 4 *
        figureOneDependentPhaseCount q) *
        dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedSecond q I mu W)
          (figureOneDependentPhaseCount q) ≤
      (1 + q.eps ^ 2 / 16) *
        dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedMean q I mu W)
          (figureOneDependentPhaseCount q) ^ 2 := by
  let m := figureOneDependentPhaseCount q
  let meanProduct := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu W) m
  have hm2 := figureOneChronologicalTruncatedSecondProduct_reset_normalized
    q I mu W hWmeas hW0 hWmem hWmean hWsecond (le_refl m)
  have hmult := figureOneResetReference_momentMultiplier_le
    q hepsilon0 hepsilon (le_refl m)
  have hmult0 : 0 ≤ 1 + 2 * epsilon *
      figureOneDependentAlpha q ^ 4 * (m : ℝ) := by positivity
  calc
    _ ≤ (1 + 2 * epsilon * figureOneDependentAlpha q ^ 4 * m) *
        ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
      mul_le_mul_of_nonneg_left hm2 hmult0
    _ ≤ ((1 + 5 * q.eps ^ 2 / 4096) *
          (1 + q.eps ^ 2 / 32)) * meanProduct ^ 2 := by
      have hs := mul_le_mul_of_nonneg_right hmult
        (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (figureOneResetReference_momentBudget_le q) (sq_nonneg meanProduct)

/-! ## Reference-side Lemma 7.15 -/

/-- Lemma 7.15 for one global chronological reset-reference law.  Its
coordinates have the exact paper means, the equation-(6) second moments with
`slack/8`, and the transported Lemma 7.17 coefficient. -/
theorem measure_chronologicalResetReferencePhaseSampleProduct_figureOne_le
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      (figureOneChronologicalMomentFactor q j +
          figureOneExecutableMomentSlack q / 8) *
        figureOneChronologicalRawMean q I j ^ 2)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ (5 / 2 : ℝ) * figureOneDependentEpsilon q)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun epsilon
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I mu W)
          (figureOneChronologicalTruncatedPhase q I W) i)
        (figureOneChronologicalTruncatedPhase q I W (i + 1)) mu) :
    mu {omega | (5 * q.eps / 8) *
          dependentPhaseMeanProduct
            (figureOneChronologicalTruncatedMean q I mu W)
            (figureOneDependentPhaseCount q) ≤
        |dependentPhaseSampleProduct W
            (figureOneDependentPhaseCount q) omega -
          dependentPhaseMeanProduct
            (figureOneChronologicalTruncatedMean q I mu W)
            (figureOneDependentPhaseCount q)|} ≤
      ENNReal.ofReal (11 / 64 : ℝ) := by
  let mean := figureOneChronologicalTruncatedMean q I mu W
  let raw := figureOneChronologicalRawMean q I
  let second := figureOneChronologicalTruncatedSecond q I mu W
  let V := figureOneChronologicalTruncatedPhase q I W
  have hWsecond' : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneResetReferenceMomentFactor q j * raw j ^ 2 := by
    simpa [figureOneResetReferenceMomentFactor, raw] using hWsecond
  have hWsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * raw j ^ 2 := fun j =>
    (hWsecond' j).trans <| mul_le_mul_of_nonneg_right
      (figureOneResetReferenceMomentFactor_le_two q j) (sq_nonneg _)
  have hmeanPos : ∀ j, 0 < mean j := fun j =>
    figureOneChronologicalTruncatedMean_pos_of_two
      q I mu W hW0 hWmem hWmean hWsecondTwo j
  have hrawPos : ∀ j, 0 < raw j := fun j =>
    figureOneChronologicalRawMean_pos q I j
  have hraw_le : ∀ j, raw j ≤ 2 * mean j := fun j =>
    figureOneChronologicalRawMean_le_two_truncatedMean_of_two
      q I mu W hW0 hWmem hWmean hWsecondTwo j
  have hmeanSecond : ∀ j, mean j ^ 2 ≤ second j := fun j =>
    figureOneChronologicalTruncatedMean_sq_le_second
      q I mu W hWmeas hW0 j
  have hrawSecond : ∀ j, raw j ^ 2 ≤ 2 * second j := fun j =>
    figureOneChronologicalRawMean_sq_le_two_truncatedSecond_of_two
      q I mu W hWmeas hW0 hWmem hWmean hWsecondTwo j
  refine (measure_dependentPhaseSampleProduct_relativeDeviation_le
    mu (figureOneDependentAlpha q) epsilon mean raw second V W
      (figureOneDependentAlpha_one_le q) hepsilon0
      (figureOneResetReference_smallness q hepsilon0 hepsilon)
      (fun j => (hmeanPos j).le) hmeanPos
      (fun j => (hrawPos j).le) hrawPos hraw_le
      (fun j => integral_nonneg fun _ => sq_nonneg _)
      hmeanSecond hrawSecond
      (fun j => figureOneChronologicalTruncatedPhase_measurable
        q I W hWmeas j)
      (fun j omega => figureOneChronologicalTruncatedPhase_nonneg
        q I W hW0 j omega)
      (fun j omega => figureOneChronologicalTruncatedPhase_le_cap q I W j omega)
      (fun _ => rfl) (fun _ => rfl)
      (figureOneDependentPhaseCount q) (fun _ _ _ _ => rfl)
      (fun j _ _ => hWmeas j) (fun j _ _ => hW0 j)
      (fun j _ _ => (hWmem j).integrable (by norm_num))
      (fun j _ _ => hWmean j) hind
      (figureOneResetReference_relativeProduct_finite
        q I mu W hWmeas hW0 hWmem hWmean hWsecond'
          hepsilon0 hepsilon)
      (fun i hi => figureOneResetReference_coefficient
        q hepsilon0 hepsilon hi)
      (tailDelta := q.eps ^ 2 / 16) (relativeEps := 5 * q.eps / 8)
      (div_nonneg (sq_nonneg q.eps) (by norm_num))
      (div_pos (mul_pos (by norm_num) q.heps.1) (by norm_num))
      (figureOneResetReference_tailSecond
        q I mu W hWmeas hW0 hWmem hWmean hWsecond'
          hepsilon0 hepsilon)).trans ?_
  exact figureOneDependent_lemma715_probability_budget q

theorem figureOneChronologicalResetReferenceTruncatedMeanProduct_relativeApprox
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      (figureOneChronologicalMomentFactor q j +
          figureOneExecutableMomentSlack q / 8) *
        figureOneChronologicalRawMean q I j ^ 2) :
    RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (figureOneChronologicalTruncatedMean q I mu W)
        (figureOneDependentPhaseCount q)) := by
  have hsecondTwo : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      2 * figureOneChronologicalRawMean q I j ^ 2 := fun j =>
    (hWsecond j).trans <| mul_le_mul_of_nonneg_right
      (figureOneResetReferenceMomentFactor_le_two q j) (sq_nonneg _)
  exact figureOneChronologicalTruncatedMeanProduct_relativeApprox_of_two
    q I mu W hWmeas hW0 hWmem hWmean hsecondTwo

/-- End-to-end post-initial adapter for a global chronological reset
reference.  The executable side is used only through the final mapped-product
comparison, while all Lemma 7.15 moments live on `reference`. -/
theorem figureOnePostInitialDirectFailureBoundFor_of_resetReferenceMappedProductLe
    {Actual Reference : Type*}
    [MeasurableSpace Actual] [MeasurableSpace Reference]
    (q : VolumeParams) (I : VolumeInput q.n)
    (continuation : AmbientSpace q.n → Measure ℝ)
    (htrunc : FigureOneRadialTruncationBound q I)
    (actualLaw : Measure Actual) (reference : Measure Reference)
    [IsProbabilityMeasure reference]
    (actualProduct : Actual → ℝ) (W : ℕ → Reference → ℝ)
    (hactualMeas : Measurable actualProduct)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j state, 0 ≤ W j state)
    (hWmem : ∀ j, MemLp (W j) 2 reference)
    (hWmean : ∀ j, (∫ state, W j state ∂reference) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ state, W j state ^ 2 ∂reference) ≤
      (figureOneChronologicalMomentFactor q j +
          figureOneExecutableMomentSlack q / 8) *
        figureOneChronologicalRawMean q I j ^ 2)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ (5 / 2 : ℝ) * figureOneDependentEpsilon q)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun epsilon
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I reference W)
          (figureOneChronologicalTruncatedPhase q I W) i)
        (figureOneChronologicalTruncatedPhase q I W (i + 1)) reference)
    (htransfer : MeasureLeUpTo
      (actualLaw.map
        (fun state => initialGaussianIntegral q * actualProduct state))
      (reference.map (fun state => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) state))
      (ENNReal.ofReal (1 / 64 : ℝ)))
    (hlaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          continuation =
        actualLaw.map
          (fun state => initialGaussianIntegral q * actualProduct state)) :
    FigureOnePostInitialDirectFailureBoundFor q I continuation := by
  let referenceProduct : Reference → ℝ :=
    dependentPhaseSampleProduct W (figureOneDependentPhaseCount q)
  let mean := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I reference W)
      (figureOneDependentPhaseCount q)
  have hrefMeas : Measurable referenceProduct := by
    unfold referenceProduct dependentPhaseSampleProduct
    exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
      fun j _ => hWmeas (j + 1)
  have hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase) mean := by
    exact figureOneChronologicalResetReferenceTruncatedMeanProduct_relativeApprox
      q I reference W hWmeas hW0 hWmem hWmean hWsecond
  have htail : reference {state | (5 * q.eps / 8) * mean ≤
      |referenceProduct state - mean|} ≤ ENNReal.ofReal (11 / 64 : ℝ) := by
    simpa [referenceProduct, mean] using
      measure_chronologicalResetReferencePhaseSampleProduct_figureOne_le
        q I reference W hWmeas hW0 hWmem hWmean hWsecond
          hepsilon0 hepsilon hind
  apply figureOnePostInitialDirectFailureBoundFor_of_mappedProductLe
    q I continuation htrunc actualLaw reference actualProduct referenceProduct
      hactualMeas hrefMeas mean hmeanApprox htail
  · simpa [referenceProduct] using htransfer
  · exact hlaw

#print axioms measure_chronologicalResetReferencePhaseSampleProduct_figureOne_le
#print axioms
  figureOneChronologicalResetReferenceTruncatedMeanProduct_relativeApprox
#print axioms
  figureOnePostInitialDirectFailureBoundFor_of_resetReferenceMappedProductLe

end

end ArlibCommunity.Algorithms.CV18
