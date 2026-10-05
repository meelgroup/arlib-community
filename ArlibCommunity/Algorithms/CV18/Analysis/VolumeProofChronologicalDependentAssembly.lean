/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedHistoryMomentBridge
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExactChance

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-!
# Chronological ideal-history assembly for CV18 Lemma 7.15

The moment recurrence is run on ideal `bar-W` coordinates in the explicit
chronological phase order.  The executable history is related only at the
final finite event, so approximate stationarity is never used to claim exact
executable first or second moments.
-/

noncomputable def figureOneChronologicalTruncatedPhase
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (Wbar : ℕ → Omega → ℝ) :
    ℕ → Omega → ℝ :=
  dependentTruncatedPhase (figureOneDependentAlpha q)
    (figureOneChronologicalRawMean q I) Wbar

noncomputable def figureOneChronologicalTruncatedMean
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    (Wbar : ℕ → Omega → ℝ) (j : ℕ) : ℝ :=
  ∫ omega, figureOneChronologicalTruncatedPhase q I Wbar j omega ∂mu

noncomputable def figureOneChronologicalTruncatedSecond
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    (Wbar : ℕ → Omega → ℝ) (j : ℕ) : ℝ :=
  ∫ omega, figureOneChronologicalTruncatedPhase q I Wbar j omega ^ 2 ∂mu

theorem figureOneChronologicalTruncatedPhase_measurable
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j)) (j : ℕ) :
    Measurable (figureOneChronologicalTruncatedPhase q I Wbar j) := by
  exact (hWmeas j).min measurable_const

theorem figureOneChronologicalTruncatedPhase_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (Wbar : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega) (j : ℕ) (omega : Omega) :
    0 ≤ figureOneChronologicalTruncatedPhase q I Wbar j omega := by
  exact le_min (hW0 j omega) <| mul_nonneg
    (figureOneDependentAlpha_pos q).le
    (figureOneChronologicalRawMean_pos q I j).le

theorem figureOneChronologicalTruncatedPhase_le_cap
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (Wbar : ℕ → Omega → ℝ)
    (j : ℕ) (omega : Omega) :
    figureOneChronologicalTruncatedPhase q I Wbar j omega ≤
      figureOneDependentAlpha q * figureOneChronologicalRawMean q I j :=
  min_le_right _ _

theorem figureOneChronologicalTruncatedPhase_le
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (Wbar : ℕ → Omega → ℝ)
    (j : ℕ) (omega : Omega) :
    figureOneChronologicalTruncatedPhase q I Wbar j omega ≤ Wbar j omega :=
  min_le_left _ _

theorem figureOneChronologicalTruncatedPhase_memLp_two
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsFiniteMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega) (j : ℕ) :
    MemLp (figureOneChronologicalTruncatedPhase q I Wbar j) 2 mu := by
  apply MemLp.of_bound
    (figureOneChronologicalTruncatedPhase_measurable q I Wbar hWmeas j).aestronglyMeasurable
    (figureOneDependentAlpha q * figureOneChronologicalRawMean q I j)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg
    (figureOneChronologicalTruncatedPhase_nonneg q I Wbar hW0 j omega)]
  exact figureOneChronologicalTruncatedPhase_le_cap q I Wbar j omega

theorem figureOneChronologicalTruncatedSecond_le
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    figureOneChronologicalTruncatedSecond q I mu Wbar j ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2 := by
  have hVmem := figureOneChronologicalTruncatedPhase_memLp_two
    q I mu Wbar hWmeas hW0 j
  have hle : figureOneChronologicalTruncatedSecond q I mu Wbar j ≤
      ∫ omega, Wbar j omega ^ 2 ∂mu := by
    apply integral_mono hVmem.integrable_sq (hWmem j).integrable_sq
    intro omega
    exact (sq_le_sq₀
      (figureOneChronologicalTruncatedPhase_nonneg q I Wbar hW0 j omega)
      (hW0 j omega)).2
        (figureOneChronologicalTruncatedPhase_le q I Wbar j omega)
  exact hle.trans (hWsecond j)

theorem figureOneChronologicalTruncatedMean_sq_le_second
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega) (j : ℕ) :
    figureOneChronologicalTruncatedMean q I mu Wbar j ^ 2 ≤
      figureOneChronologicalTruncatedSecond q I mu Wbar j := by
  have hmem := figureOneChronologicalTruncatedPhase_memLp_two
    q I mu Wbar hWmeas hW0 j
  have hdev : 0 ≤ ∫ omega,
      (figureOneChronologicalTruncatedPhase q I Wbar j omega -
        figureOneChronologicalTruncatedMean q I mu Wbar j) ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  rw [integral_sub_const_sq_eq mu hmem
    (figureOneChronologicalTruncatedMean q I mu Wbar j)] at hdev
  dsimp only [figureOneChronologicalTruncatedMean,
    figureOneChronologicalTruncatedSecond] at hdev ⊢
  nlinarith

theorem figureOneChronologicalTruncatedMean_lower
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    (1 - 1 / (2 * figureOneDependentAlpha q)) *
        figureOneChronologicalRawMean q I j ≤
      figureOneChronologicalTruncatedMean q I mu Wbar j := by
  let raw := figureOneChronologicalRawMean q I j
  let alpha := figureOneDependentAlpha q
  have hraw : 0 < raw := figureOneChronologicalRawMean_pos q I j
  have halpha : (1024 : ℝ) ≤ alpha := figureOneDependentAlpha_ge_1024 q
  have hcap : 0 < alpha * raw := mul_pos (by linarith) hraw
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    ((hWmem j).integrable (by norm_num)) (hWmem j).integrable_sq
      (hW0 j) hcap
  have hfactor : figureOneChronologicalMomentFactor q j ≤ 2 :=
    figureOneIdealPhaseFactor_le_two q _
  have hsecond : (∫ omega, Wbar j omega ^ 2 ∂mu) ≤ 2 * raw ^ 2 :=
    (hWsecond j).trans <| mul_le_mul_of_nonneg_right hfactor (sq_nonneg raw)
  have hloss : (∫ omega, Wbar j omega ^ 2 ∂mu) /
      (4 * (alpha * raw)) ≤ raw / (2 * alpha) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hcap)]
    field_simp [show alpha ≠ 0 by linarith]
    nlinarith [hsecond]
  rw [hWmean j] at htrunc
  change (1 - 1 / (2 * alpha)) * raw ≤
    ∫ omega, min (Wbar j omega) (alpha * raw) ∂mu
  calc
    _ = raw - raw / (2 * alpha) := by ring
    _ ≤ raw - (∫ omega, Wbar j omega ^ 2 ∂mu) /
        (4 * (alpha * raw)) := sub_le_sub_left hloss raw
    _ ≤ _ := htrunc

theorem figureOneChronologicalRawMean_le_one_add_inv_mul_mean
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    figureOneChronologicalRawMean q I j ≤
      (1 + 1 / figureOneDependentAlpha q) *
        figureOneChronologicalTruncatedMean q I mu Wbar j := by
  let raw := figureOneChronologicalRawMean q I j
  let alpha := figureOneDependentAlpha q
  have hraw : 0 < raw := figureOneChronologicalRawMean_pos q I j
  have halpha : (1024 : ℝ) ≤ alpha := figureOneDependentAlpha_ge_1024 q
  have hlower := figureOneChronologicalTruncatedMean_lower
    q I mu Wbar hW0 hWmem hWmean hWsecond j
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
    figureOneChronologicalTruncatedMean q I mu Wbar j
  calc
    raw = 1 * raw := by ring
    _ ≤ ((1 + 1 / alpha) * (1 - 1 / (2 * alpha))) * raw :=
      mul_le_mul_of_nonneg_right hcoefficient hraw.le
    _ = (1 + 1 / alpha) * ((1 - 1 / (2 * alpha)) * raw) := by ring
    _ ≤ _ := hscale

theorem figureOneChronologicalTruncatedMean_pos
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    0 < figureOneChronologicalTruncatedMean q I mu Wbar j := by
  have hlower := figureOneChronologicalTruncatedMean_lower
    q I mu Wbar hW0 hWmem hWmean hWsecond j
  have ha := figureOneDependentAlpha_ge_1024 q
  have hr := figureOneChronologicalRawMean_pos q I j
  have hap : 0 < figureOneDependentAlpha q := figureOneDependentAlpha_pos q
  have hinv : 1 / (2 * figureOneDependentAlpha q) ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hap)]
    nlinarith
  have hc : (3 / 4 : ℝ) ≤
      1 - 1 / (2 * figureOneDependentAlpha q) := by linarith
  exact (mul_pos (lt_of_lt_of_le (by norm_num) hc) hr).trans_le hlower

theorem figureOneChronologicalRawMean_le_two_truncatedMean
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    figureOneChronologicalRawMean q I j ≤
      2 * figureOneChronologicalTruncatedMean q I mu Wbar j := by
  have hlower := figureOneChronologicalTruncatedMean_lower
    q I mu Wbar hW0 hWmem hWmean hWsecond j
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

theorem figureOneChronologicalRawMean_sq_le_two_truncatedSecond
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) (j : ℕ) :
    figureOneChronologicalRawMean q I j ^ 2 ≤
      2 * figureOneChronologicalTruncatedSecond q I mu Wbar j := by
  have hlower := figureOneChronologicalTruncatedMean_lower
    q I mu Wbar hW0 hWmem hWmean hWsecond j
  have hm0 := (figureOneChronologicalTruncatedMean_pos
    q I mu Wbar hW0 hWmem hWmean hWsecond j).le
  have hr0 := (figureOneChronologicalRawMean_pos q I j).le
  have ha := figureOneDependentAlpha_ge_1024 q
  have hc : (3 / 4 : ℝ) * figureOneChronologicalRawMean q I j ≤
      figureOneChronologicalTruncatedMean q I mu Wbar j := by
    have hap : 0 < figureOneDependentAlpha q := figureOneDependentAlpha_pos q
    have hinv : 1 / (2 * figureOneDependentAlpha q) ≤ (1 / 4 : ℝ) := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hap)]
      nlinarith
    have hcoef : (3 / 4 : ℝ) ≤
        1 - 1 / (2 * figureOneDependentAlpha q) := by linarith
    exact (mul_le_mul_of_nonneg_right hcoef hr0).trans hlower
  have hsq : ((3 / 4 : ℝ) *
      figureOneChronologicalRawMean q I j) ^ 2 ≤
      figureOneChronologicalTruncatedMean q I mu Wbar j ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) hr0) hm0).2 hc
  have hm2 := figureOneChronologicalTruncatedMean_sq_le_second
    q I mu Wbar hWmeas hW0 j
  nlinarith [sq_nonneg (figureOneChronologicalRawMean q I j)]

theorem figureOneChronologicalTruncatedMean_le_rawMean
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j) (j : ℕ) :
    figureOneChronologicalTruncatedMean q I mu Wbar j ≤
      figureOneChronologicalRawMean q I j := by
  rw [← hWmean j]
  apply integral_mono
    ((figureOneChronologicalTruncatedPhase_memLp_two
      q I mu Wbar hWmeas hW0 j).integrable (by norm_num))
    ((hWmem j).integrable (by norm_num))
  exact figureOneChronologicalTruncatedPhase_le q I Wbar j

theorem figureOneChronologicalMomentFactor_partialProduct_le_exp
    (q : VolumeParams) {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct (figureOneChronologicalMomentFactor q) i ≤
      Real.exp (13 * q.eps ^ 2 / 512) := by
  have hmono := Finset.prod_mono_set_of_one_le
    (f := fun j => figureOneChronologicalMomentFactor q (j + 1))
    (fun j => figureOneChronologicalMomentFactor_one_le q (j + 1))
    (Finset.range_mono hi)
  unfold dependentPhaseMeanProduct
  refine hmono.trans ?_
  change dependentPhaseMeanProduct (figureOneChronologicalMomentFactor q)
    (figureOneDependentPhaseCount q) ≤ _
  rw [figureOneChronologicalMomentFactor_product]
  exact figureOneIdealPhaseFactor_product_le q

theorem figureOneChronologicalRawMeanProduct_le
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) (i : ℕ) :
    dependentPhaseMeanProduct (figureOneChronologicalRawMean q I) i ≤
      (1 + 1 / figureOneDependentAlpha q) ^ i *
        dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedMean q I mu Wbar) i := by
  unfold dependentPhaseMeanProduct
  calc
    (∏ j ∈ Finset.range i, figureOneChronologicalRawMean q I (j + 1)) ≤
        ∏ j ∈ Finset.range i,
          ((1 + 1 / figureOneDependentAlpha q) *
            figureOneChronologicalTruncatedMean q I mu Wbar (j + 1)) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact (figureOneChronologicalRawMean_pos q I (j + 1)).le
      · intro j hj
        exact figureOneChronologicalRawMean_le_one_add_inv_mul_mean
          q I mu Wbar hW0 hWmem hWmean hWsecond (j + 1)
    _ = (1 + 1 / figureOneDependentAlpha q) ^ i *
        ∏ j ∈ Finset.range i,
          figureOneChronologicalTruncatedMean q I mu Wbar (j + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

theorem figureOneChronologicalTruncatedMeanProduct_le_raw
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j) (i : ℕ) :
    dependentPhaseMeanProduct
        (figureOneChronologicalTruncatedMean q I mu Wbar) i ≤
      dependentPhaseMeanProduct (figureOneChronologicalRawMean q I) i := by
  unfold dependentPhaseMeanProduct
  apply Finset.prod_le_prod
  · intro j hj
    exact integral_nonneg fun omega =>
      figureOneChronologicalTruncatedPhase_nonneg q I Wbar hW0 (j + 1) omega
  · intro j hj
    exact figureOneChronologicalTruncatedMean_le_rawMean
      q I mu Wbar hWmeas hW0 hWmem hWmean (j + 1)

theorem figureOneChronologicalTruncatedSecondProduct_le
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) (i : ℕ) :
    dependentPhaseMeanProduct
        (figureOneChronologicalTruncatedSecond q I mu Wbar) i ≤
      dependentPhaseMeanProduct (figureOneChronologicalMomentFactor q) i *
        dependentPhaseMeanProduct (figureOneChronologicalRawMean q I) i ^ 2 := by
  unfold dependentPhaseMeanProduct
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro j hj
    exact integral_nonneg fun _ => sq_nonneg _
  · intro j hj
    exact figureOneChronologicalTruncatedSecond_le
      q I mu Wbar hWmeas hW0 hWmem hWsecond (j + 1)

theorem figureOneChronologicalTruncatedSecondProduct_normalized
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct
        (figureOneChronologicalTruncatedSecond q I mu Wbar) i ≤
      (1 + q.eps ^ 2 / 32) *
        dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedMean q I mu Wbar) i ^ 2 := by
  let meanProduct := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu Wbar) i
  let rawProduct := dependentPhaseMeanProduct
    (figureOneChronologicalRawMean q I) i
  let factorProduct := dependentPhaseMeanProduct
    (figureOneChronologicalMomentFactor q) i
  have hmean0 : 0 ≤ meanProduct := dependentPhaseMeanProduct_nonneg _
    (fun j => (figureOneChronologicalTruncatedMean_pos
      q I mu Wbar hW0 hWmem hWmean hWsecond j).le) i
  have hraw0 : 0 ≤ rawProduct := dependentPhaseMeanProduct_nonneg _
    (fun j => (figureOneChronologicalRawMean_pos q I j).le) i
  have hraw := figureOneChronologicalRawMeanProduct_le
    q I mu Wbar hW0 hWmem hWmean hWsecond i
  have hpow := figureOne_one_add_inv_alpha_pow_le_exp q hi
  have hrawExp : rawProduct ≤
      Real.exp (q.eps ^ 2 / 1024) * meanProduct :=
    hraw.trans (mul_le_mul_of_nonneg_right hpow hmean0)
  have hrawSq : rawProduct ^ 2 ≤
      Real.exp (q.eps ^ 2 / 1024) ^ 2 * meanProduct ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hraw0
      (mul_nonneg (Real.exp_pos _).le hmean0)).2 hrawExp
  have hsecond := figureOneChronologicalTruncatedSecondProduct_le
    q I mu Wbar hWmeas hW0 hWmem hWsecond i
  have hfactor := figureOneChronologicalMomentFactor_partialProduct_le_exp q hi
  have hbound : factorProduct * rawProduct ^ 2 ≤
      Real.exp (13 * q.eps ^ 2 / 512) *
        (Real.exp (q.eps ^ 2 / 1024) ^ 2 * meanProduct ^ 2) :=
    mul_le_mul hfactor hrawSq (sq_nonneg rawProduct) (Real.exp_pos _).le
  have hexp : Real.exp (13 * q.eps ^ 2 / 512) *
      Real.exp (q.eps ^ 2 / 1024) ^ 2 =
      Real.exp (7 * q.eps ^ 2 / 256) := by
    rw [show Real.exp (q.eps ^ 2 / 1024) ^ 2 =
      Real.exp (2 * (q.eps ^ 2 / 1024)) by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring,
      ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ factorProduct * rawProduct ^ 2 := hsecond
    _ ≤ _ := hbound
    _ = Real.exp (7 * q.eps ^ 2 / 256) * meanProduct ^ 2 := by
      rw [← mul_assoc, hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (figureOne_exp_seven_eps_sq_div_256_le q) (sq_nonneg meanProduct)

theorem figureOneChronological_relativeProduct_finite
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) :
    ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (figureOneChronologicalTruncatedSecond q I mu Wbar) i ≤
        2 * dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedMean q I mu Wbar) i ^ 2 := by
  intro i hi
  let meanProduct := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu Wbar) i
  have hm2 := figureOneChronologicalTruncatedSecondProduct_normalized
    q I mu Wbar hWmeas hW0 hWmem hWmean hWsecond hi
  have hmult := figureOneDependentMomentMultiplier_le q hi
  have hmult0 : 0 ≤ 1 + 2 * figureOneDependentEpsilon q *
      figureOneDependentAlpha q ^ 4 * (i : ℝ) := by
    have : 0 ≤ 2 * figureOneDependentEpsilon q *
        figureOneDependentAlpha q ^ 4 * (i : ℝ) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num)
          (figureOneDependentEpsilon_nonneg q)) (by positivity))
        (Nat.cast_nonneg i)
    linarith
  have hbudget := figureOneDependentMomentBudget_le q
  have heps2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  have htwo : 1 + q.eps ^ 2 / 16 ≤ (2 : ℝ) := by nlinarith
  calc
    _ ≤ (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
        ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
      mul_le_mul_of_nonneg_left hm2 hmult0
    _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
        meanProduct ^ 2 := by
      have hs := mul_le_mul_of_nonneg_right hmult
        (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
      nlinarith
    _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right hbudget (sq_nonneg meanProduct)
    _ ≤ 2 * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right htwo (sq_nonneg meanProduct)

theorem figureOneChronological_tailSecond
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) :
    (1 + 2 * figureOneDependentEpsilon q *
        figureOneDependentAlpha q ^ 4 * figureOneDependentPhaseCount q) *
        dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedSecond q I mu Wbar)
          (figureOneDependentPhaseCount q) ≤
      (1 + q.eps ^ 2 / 16) *
        dependentPhaseMeanProduct
          (figureOneChronologicalTruncatedMean q I mu Wbar)
          (figureOneDependentPhaseCount q) ^ 2 := by
  let m := figureOneDependentPhaseCount q
  let meanProduct := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu Wbar) m
  have hm2 := figureOneChronologicalTruncatedSecondProduct_normalized
    q I mu Wbar hWmeas hW0 hWmem hWmean hWsecond (le_refl m)
  have hmult := figureOneDependentMomentMultiplier_le q (le_refl m)
  have hmult0 : 0 ≤ 1 + 2 * figureOneDependentEpsilon q *
      figureOneDependentAlpha q ^ 4 * (m : ℝ) := by
    have : 0 ≤ 2 * figureOneDependentEpsilon q *
        figureOneDependentAlpha q ^ 4 * (m : ℝ) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num)
          (figureOneDependentEpsilon_nonneg q)) (by positivity))
        (Nat.cast_nonneg m)
    linarith
  calc
    _ ≤ (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * m) *
        ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
      mul_le_mul_of_nonneg_left hm2 hmult0
    _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
        meanProduct ^ 2 := by
      have hs := mul_le_mul_of_nonneg_right hmult
        (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (figureOneDependentMomentBudget_le q) (sq_nonneg meanProduct)

theorem figureOneChronologicalTruncatedMeanProduct_relativeApprox
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2) :
    RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (figureOneChronologicalTruncatedMean q I mu Wbar)
        (figureOneDependentPhaseCount q)) := by
  rw [← figureOneChronologicalRawMean_product q I]
  let raw := dependentPhaseMeanProduct
    (figureOneChronologicalRawMean q I) (figureOneDependentPhaseCount q)
  let mean := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu Wbar)
      (figureOneDependentPhaseCount q)
  have hrawPos : 0 < raw := by
    apply Finset.prod_pos
    intro j hj
    exact figureOneChronologicalRawMean_pos q I (j + 1)
  have hmean0 : 0 ≤ mean := dependentPhaseMeanProduct_nonneg _
    (fun j => integral_nonneg fun omega =>
      figureOneChronologicalTruncatedPhase_nonneg q I Wbar hW0 j omega) _
  have hmeanRaw : mean ≤ raw :=
    figureOneChronologicalTruncatedMeanProduct_le_raw
      q I mu Wbar hWmeas hW0 hWmem hWmean _
  have hrawPow := figureOneChronologicalRawMeanProduct_le
    q I mu Wbar hW0 hWmem hWmean hWsecond
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

/-- Lemma 7.15 specialized to the explicit chronological ideal `bar-W`
coordinates.  Exact first and second moments belong only to this auxiliary
ideal probability space. -/
theorem measure_chronologicalIdealPhaseSampleProduct_figureOne_le
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (Wbar : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j omega, 0 ≤ Wbar j omega)
    (hWmem : ∀ j, MemLp (Wbar j) 2 mu)
    (hWmean : ∀ j, (∫ omega, Wbar j omega ∂mu) =
      figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, Wbar j omega ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I mu Wbar)
        (figureOneChronologicalTruncatedPhase q I Wbar) i)
      (figureOneChronologicalTruncatedPhase q I Wbar (i + 1)) mu) :
    mu {omega | (5 * q.eps / 8) *
          dependentPhaseMeanProduct
            (figureOneChronologicalTruncatedMean q I mu Wbar)
            (figureOneDependentPhaseCount q) ≤
        |dependentPhaseSampleProduct Wbar
            (figureOneDependentPhaseCount q) omega -
          dependentPhaseMeanProduct
            (figureOneChronologicalTruncatedMean q I mu Wbar)
            (figureOneDependentPhaseCount q)|} ≤
      ENNReal.ofReal (11 / 64 : ℝ) := by
  let mean := figureOneChronologicalTruncatedMean q I mu Wbar
  let raw := figureOneChronologicalRawMean q I
  let second := figureOneChronologicalTruncatedSecond q I mu Wbar
  let V := figureOneChronologicalTruncatedPhase q I Wbar
  have hmeanPos : ∀ j, 0 < mean j := fun j =>
    figureOneChronologicalTruncatedMean_pos
      q I mu Wbar hW0 hWmem hWmean hWsecond j
  have hrawPos : ∀ j, 0 < raw j := fun j =>
    figureOneChronologicalRawMean_pos q I j
  have hraw_le : ∀ j, raw j ≤ 2 * mean j := fun j =>
    figureOneChronologicalRawMean_le_two_truncatedMean
      q I mu Wbar hW0 hWmem hWmean hWsecond j
  have hmeanSecond : ∀ j, mean j ^ 2 ≤ second j := fun j =>
    figureOneChronologicalTruncatedMean_sq_le_second
      q I mu Wbar hWmeas hW0 j
  have hrawSecond : ∀ j, raw j ^ 2 ≤ 2 * second j := fun j =>
    figureOneChronologicalRawMean_sq_le_two_truncatedSecond
      q I mu Wbar hWmeas hW0 hWmem hWmean hWsecond j
  apply measure_dependentPhaseSampleProduct_figureOne_le
    q mu mean raw second V Wbar
  · exact fun j => (hmeanPos j).le
  · exact hmeanPos
  · exact fun j => (hrawPos j).le
  · exact hrawPos
  · exact hraw_le
  · exact fun j => integral_nonneg fun _ => sq_nonneg _
  · exact hmeanSecond
  · exact hrawSecond
  · exact fun j => figureOneChronologicalTruncatedPhase_measurable
      q I Wbar hWmeas j
  · exact fun j omega => figureOneChronologicalTruncatedPhase_nonneg
      q I Wbar hW0 j omega
  · exact fun j omega => figureOneChronologicalTruncatedPhase_le_cap
      q I Wbar j omega
  · exact fun j => rfl
  · exact fun j => rfl
  · exact fun j _ _ omega => rfl
  · exact fun j _ _ => hWmeas j
  · exact fun j _ _ omega => hW0 j omega
  · exact fun j _ _ => (hWmem j).integrable (by norm_num)
  · exact fun j _ _ => hWmean j
  · exact hind
  · exact figureOneChronological_relativeProduct_finite
      q I mu Wbar hWmeas hW0 hWmem hWmean hWsecond
  · exact figureOneChronological_tailSecond
      q I mu Wbar hWmeas hW0 hWmem hWmean hWsecond

/-- The exact-chance replacement budget is far below the `1/64` slot used
by the direct post-initial failure assembly. -/
theorem figureOne_exactChance_event_budget_le (q : VolumeParams) :
    (figureOneDependentMaxSampleCount q * figureOneDependentPhaseCount q) •
        ENNReal.ofReal (figureOnePerSampleMixingError q) ≤
      ENNReal.ofReal (1 / 64 : ℝ) := by
  let error := (figureOneDependentMaxSampleCount q *
      figureOneDependentPhaseCount q) •
        ENNReal.ofReal (figureOnePerSampleMixingError q)
  have herrTop : error ≠ ⊤ := by
    dsimp [error]
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  rw [← ENNReal.toReal_le_toReal herrTop ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 64)]
  have heq : 3 * error.toReal = figureOneDependentEpsilon q := by
    simpa [error] using figureOne_exactChance_budget q
  have hdep0 := figureOneDependentEpsilon_nonneg q
  have ha := figureOneDependentAlpha_ge_1024 q
  have ha2 : (2 : ℝ) ≤ figureOneDependentAlpha q := by linarith
  have hpow : (8 : ℝ) ≤ figureOneDependentAlpha q ^ 3 := by
    calc
      (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ figureOneDependentAlpha q ^ 3 :=
        pow_le_pow_left₀ (by norm_num) ha2 3
  have hsmall := figureOneDependent_smallness q
  have hscaled : 4 * figureOneDependentEpsilon q * (16 / 3 : ℝ) ≤
      4 * figureOneDependentEpsilon q * figureOneDependentAlpha q ^ 3 := by
    have h163 : (16 / 3 : ℝ) ≤ figureOneDependentAlpha q ^ 3 := by
      norm_num at hpow ⊢
      linarith
    exact mul_le_mul_of_nonneg_left h163
      (mul_nonneg (by norm_num) hdep0)
  have hdep : figureOneDependentEpsilon q ≤ (3 / 64 : ℝ) := by
    nlinarith
  nlinarith

/-- The Lemma 7.17(c) independence premise for any chronological accumulated
product/next-phase pair follows from the shared ExactChance construction.
The sole model-specific premise is its integrated ideal-prefix step bound. -/
theorem figureOneChronologicalApproxIndep_of_exactChance
    {State S T : Type*} [MeasurableSpace State]
    [MeasurableSpace S] [MeasurableSpace T]
    (q : VolumeParams)
    (actualK idealK : ℕ → State → Measure State)
    (initial : Measure State) [IsProbabilityMeasure initial]
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hidealMeas : ∀ i, Measurable (idealK i))
    (hidealProb : ∀ i state, IsProbabilityMeasure (idealK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK initial i).bind (actualK i))
        (iteratedKernelLaw idealK initial (i + 1))
        (ENNReal.ofReal (figureOnePerSampleMixingError q)))
    (X : State → S) (Y : State → T)
    (hX : Measurable X) (hY : Measurable Y)
    (hexact : ApproxIndepFun 0 X Y
      (iteratedKernelLaw idealK initial
        (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q))) :
    ApproxIndepFun (figureOneDependentEpsilon q) X Y
      (iteratedKernelLaw actualK initial
        (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q)) :=
  ApproxIndepFun.of_figureOne_exactChance q actualK idealK initial
    hactualMeas hactualProb hidealMeas hidealProb hstep X Y hX hY hexact

/-- Finite-horizon exact-chance wrapper for the output of Lemma 7.15.  It
uses only measurability of the chronological coordinates actually multiplied;
all moment and independence premises have already been discharged into
`htail`. -/
theorem figureOnePostInitialDirectFailureBoundFor_of_finiteDeviationExactChance
    {State : Type*} [MeasurableSpace State]
    (q : VolumeParams) (I : VolumeInput q.n)
    (continuation : AmbientSpace q.n → Measure ℝ)
    (htrunc : FigureOneRadialTruncationBound q I)
    (actualK idealK : ℕ → State → Measure State)
    (initial : Measure State) [IsProbabilityMeasure initial]
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hidealMeas : ∀ i, Measurable (idealK i))
    (hidealProb : ∀ i state, IsProbabilityMeasure (idealK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK initial i).bind (actualK i))
        (iteratedKernelLaw idealK initial (i + 1))
        (ENNReal.ofReal (figureOnePerSampleMixingError q)))
    (Wbar : ℕ → State → ℝ)
    (hWmeas : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      Measurable (Wbar j))
    (mean : ℝ)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ i, figureOneIdealPhaseMean q I i) mean)
    (htail :
      let idealLaw := iteratedKernelLaw idealK initial
        (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q)
      idealLaw {state | (5 * q.eps / 8) * mean ≤
        |dependentPhaseSampleProduct Wbar
            (figureOneDependentPhaseCount q) state - mean|} ≤
          ENNReal.ofReal (11 / 64 : ℝ))
    (hlaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          continuation =
        (iteratedKernelLaw actualK initial
          (figureOneDependentMaxSampleCount q *
            figureOneDependentPhaseCount q)).map
          (fun state => initialGaussianIntegral q *
            dependentPhaseSampleProduct Wbar
              (figureOneDependentPhaseCount q) state)) :
    FigureOnePostInitialDirectFailureBoundFor q I continuation := by
  let t := figureOneDependentMaxSampleCount q *
    figureOneDependentPhaseCount q
  let idealLaw := iteratedKernelLaw idealK initial t
  let actualLaw := iteratedKernelLaw actualK initial t
  let X := dependentPhaseSampleProduct Wbar (figureOneDependentPhaseCount q)
  let output : State → ℝ := fun state => initialGaussianIntegral q * X state
  let _ : IsProbabilityMeasure idealLaw :=
    iteratedKernelLaw_isProbabilityMeasure idealK initial inferInstance
      hidealMeas hidealProb t
  have hX : Measurable X := by
    dsimp only [X, dependentPhaseSampleProduct]
    exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
      fun j hj => hWmeas (j + 1) (by omega)
        (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))
  have houtput : Measurable output := measurable_const.mul hX
  have hidealFailure :
      idealLaw {state | output state ∉ accurateOutcome q I} ≤
        ENNReal.ofReal (11 / 64 : ℝ) := by
    simpa [output, X, idealLaw, t] using
      measure_scaledDependentProduct_failure_le_of_relativeDeviation
        q I htrunc idealLaw X hmeanApprox htail
  have hevent := measure_map_iteratedKernelLaw_event_le_exactChance
    actualK idealK initial hactualMeas hactualProb hstep t output houtput
      (accurateOutcome q I)ᶜ
  have hidealMap : idealLaw.map output (accurateOutcome q I)ᶜ =
      idealLaw {state | output state ∉ accurateOutcome q I} := by
    rw [Measure.map_apply houtput (accurateOutcome_measurable q I).compl]
    rfl
  unfold FigureOnePostInitialDirectFailureBoundFor
  rw [hlaw]
  calc
    actualLaw.map output (accurateOutcome q I)ᶜ ≤
        idealLaw.map output (accurateOutcome q I)ᶜ +
          t • ENNReal.ofReal (figureOnePerSampleMixingError q) := by
      simpa [actualLaw, idealLaw, t] using hevent
    _ = idealLaw {state | output state ∉ accurateOutcome q I} +
          t • ENNReal.ofReal (figureOnePerSampleMixingError q) := by
      rw [hidealMap]
    _ ≤ ENNReal.ofReal (11 / 64 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add hidealFailure (by
        simpa [t] using figureOne_exactChance_event_budget_le q)
    _ = ENNReal.ofReal (3 / 16 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 11 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      congr 1
      norm_num

/-- Final event transfer with different executable and ideal history spaces.
This is the interface used by the balanced history law: its only probabilistic
bridge is a finite additive domination between the two mapped scalar laws. -/
theorem figureOnePostInitialDirectFailureBoundFor_of_mappedProductLe
    {Actual Ideal : Type*} [MeasurableSpace Actual] [MeasurableSpace Ideal]
    (q : VolumeParams) (I : VolumeInput q.n)
    (continuation : AmbientSpace q.n → Measure ℝ)
    (htrunc : FigureOneRadialTruncationBound q I)
    (actualLaw : Measure Actual) (idealLaw : Measure Ideal)
    [IsProbabilityMeasure idealLaw]
    (actualProduct : Actual → ℝ) (idealProduct : Ideal → ℝ)
    (hactualMeas : Measurable actualProduct)
    (hidealMeas : Measurable idealProduct)
    (mean : ℝ)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ i, figureOneIdealPhaseMean q I i) mean)
    (hidealTail : idealLaw {state | (5 * q.eps / 8) * mean ≤
      |idealProduct state - mean|} ≤ ENNReal.ofReal (11 / 64 : ℝ))
    (htransfer : MeasureLeUpTo
      (actualLaw.map (fun state => initialGaussianIntegral q * actualProduct state))
      (idealLaw.map (fun state => initialGaussianIntegral q * idealProduct state))
      (ENNReal.ofReal (1 / 64 : ℝ)))
    (hlaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          continuation =
        actualLaw.map
          (fun state => initialGaussianIntegral q * actualProduct state)) :
    FigureOnePostInitialDirectFailureBoundFor q I continuation := by
  let actualOutput : Actual → ℝ := fun state =>
    initialGaussianIntegral q * actualProduct state
  let idealOutput : Ideal → ℝ := fun state =>
    initialGaussianIntegral q * idealProduct state
  have hactualOutput : Measurable actualOutput :=
    measurable_const.mul hactualMeas
  have hidealOutput : Measurable idealOutput := measurable_const.mul hidealMeas
  have hidealFailure :
      idealLaw {state | idealOutput state ∉ accurateOutcome q I} ≤
        ENNReal.ofReal (11 / 64 : ℝ) := by
    simpa [idealOutput] using
      measure_scaledDependentProduct_failure_le_of_relativeDeviation
        q I htrunc idealLaw idealProduct hmeanApprox hidealTail
  have hidealMap : idealLaw.map idealOutput (accurateOutcome q I)ᶜ =
      idealLaw {state | idealOutput state ∉ accurateOutcome q I} := by
    rw [Measure.map_apply hidealOutput (accurateOutcome_measurable q I).compl]
    rfl
  unfold FigureOnePostInitialDirectFailureBoundFor
  rw [hlaw]
  change actualLaw.map actualOutput (accurateOutcome q I)ᶜ ≤ _
  calc
    actualLaw.map actualOutput (accurateOutcome q I)ᶜ ≤
        idealLaw.map idealOutput (accurateOutcome q I)ᶜ +
          ENNReal.ofReal (1 / 64 : ℝ) := by
      exact htransfer.event_le _
    _ = idealLaw {state | idealOutput state ∉ accurateOutcome q I} +
          ENNReal.ofReal (1 / 64 : ℝ) := by rw [hidealMap]
    _ ≤ ENNReal.ofReal (11 / 64 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add hidealFailure le_rfl
    _ = ENNReal.ofReal (3 / 16 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 11 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      congr 1
      norm_num

/-- Strongest paper-aligned post-initial wrapper currently available.  All
moment statements concern chronological ideal `bar-W` coordinates.  The
executable law is transferred only at the final measurable failure event by
the finite exact-chance theorem. -/
theorem figureOnePostInitialDirectFailureBound_of_chronologicalExactChance
    {State : Type*} [MeasurableSpace State]
    (q : VolumeParams) (I : VolumeInput q.n)
    (continuation : AmbientSpace q.n → Measure ℝ)
    (htrunc : FigureOneRadialTruncationBound q I)
    (actualK idealK : ℕ → State → Measure State)
    (initial : Measure State) [IsProbabilityMeasure initial]
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (hidealMeas : ∀ i, Measurable (idealK i))
    (hidealProb : ∀ i state, IsProbabilityMeasure (idealK i state))
    (hstep : ∀ i,
      MeasureLeUpTo
        ((iteratedKernelLaw idealK initial i).bind (actualK i))
        (iteratedKernelLaw idealK initial (i + 1))
        (ENNReal.ofReal (figureOnePerSampleMixingError q)))
    (Wbar : ℕ → State → ℝ)
    (hWmeas : ∀ j, Measurable (Wbar j))
    (hW0 : ∀ j state, 0 ≤ Wbar j state)
    (hWmem : ∀ j, MemLp (Wbar j) 2
      (iteratedKernelLaw idealK initial
        (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q)))
    (hWmean : ∀ j,
      (∫ state, Wbar j state ∂iteratedKernelLaw idealK initial
        (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q)) =
        figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j,
      (∫ state, Wbar j state ^ 2 ∂iteratedKernelLaw idealK initial
        (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          figureOneChronologicalRawMean q I j ^ 2)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (figureOneChronologicalTruncatedMean q I
          (iteratedKernelLaw idealK initial
            (figureOneDependentMaxSampleCount q *
              figureOneDependentPhaseCount q)) Wbar)
        (figureOneChronologicalTruncatedPhase q I Wbar) i)
      (figureOneChronologicalTruncatedPhase q I Wbar (i + 1))
      (iteratedKernelLaw idealK initial
        (figureOneDependentMaxSampleCount q *
          figureOneDependentPhaseCount q)))
    (hlaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          continuation =
        (iteratedKernelLaw actualK initial
          (figureOneDependentMaxSampleCount q *
            figureOneDependentPhaseCount q)).map
          (fun state => initialGaussianIntegral q *
            dependentPhaseSampleProduct Wbar
              (figureOneDependentPhaseCount q) state)) :
    FigureOnePostInitialDirectFailureBoundFor q I continuation := by
  let t := figureOneDependentMaxSampleCount q *
    figureOneDependentPhaseCount q
  let idealLaw := iteratedKernelLaw idealK initial t
  let actualLaw := iteratedKernelLaw actualK initial t
  let X := dependentPhaseSampleProduct Wbar (figureOneDependentPhaseCount q)
  let output : State → ℝ := fun state => initialGaussianIntegral q * X state
  let _ : IsProbabilityMeasure idealLaw :=
    iteratedKernelLaw_isProbabilityMeasure idealK initial inferInstance
      hidealMeas hidealProb t
  have hX : Measurable X := by
    dsimp only [X]
    have hprod : ∀ m, Measurable (dependentPhaseSampleProduct Wbar m) := by
      intro m
      induction m with
      | zero =>
          rw [show dependentPhaseSampleProduct Wbar 0 = fun _ : State => (1 : ℝ) by
            funext state
            exact dependentPhaseSampleProduct_zero Wbar state]
          exact measurable_const
      | succ m ih =>
          rw [show dependentPhaseSampleProduct Wbar (m + 1) = fun state =>
              dependentPhaseSampleProduct Wbar m state * Wbar (m + 1) state by
            funext state
            exact dependentPhaseSampleProduct_succ Wbar m state]
          exact ih.mul (hWmeas (m + 1))
    exact hprod _
  have houtput : Measurable output := measurable_const.mul hX
  have htail := measure_chronologicalIdealPhaseSampleProduct_figureOne_le
    q I idealLaw Wbar hWmeas hW0 hWmem hWmean hWsecond hind
  have hmeanApprox :=
    figureOneChronologicalTruncatedMeanProduct_relativeApprox
      q I idealLaw Wbar hWmeas hW0 hWmem hWmean hWsecond
  have hidealFailure :
      idealLaw {state | output state ∉ accurateOutcome q I} ≤
        ENNReal.ofReal (11 / 64 : ℝ) := by
    simpa [output, X] using
      measure_scaledDependentProduct_failure_le_of_relativeDeviation
        q I htrunc idealLaw X hmeanApprox htail
  have hevent := measure_map_iteratedKernelLaw_event_le_exactChance
    actualK idealK initial hactualMeas hactualProb hstep t output houtput
      (accurateOutcome q I)ᶜ
  have hidealMap : idealLaw.map output (accurateOutcome q I)ᶜ =
      idealLaw {state | output state ∉ accurateOutcome q I} := by
    rw [Measure.map_apply houtput (accurateOutcome_measurable q I).compl]
    rfl
  unfold FigureOnePostInitialDirectFailureBoundFor
  rw [hlaw]
  calc
    actualLaw.map output (accurateOutcome q I)ᶜ ≤
        idealLaw.map output (accurateOutcome q I)ᶜ +
          t • ENNReal.ofReal (figureOnePerSampleMixingError q) := by
      simpa [actualLaw, idealLaw, t] using hevent
    _ = idealLaw {state | output state ∉ accurateOutcome q I} +
          t • ENNReal.ofReal (figureOnePerSampleMixingError q) := by
      rw [hidealMap]
    _ ≤ ENNReal.ofReal (11 / 64 : ℝ) + ENNReal.ofReal (1 / 64 : ℝ) :=
      add_le_add hidealFailure (by
        simpa [t] using figureOne_exactChance_event_budget_le q)
    _ = ENNReal.ofReal (3 / 16 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 11 / 64)
        (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      norm_num

#print axioms measure_chronologicalIdealPhaseSampleProduct_figureOne_le
#print axioms figureOneChronologicalTruncatedMeanProduct_relativeApprox
#print axioms figureOneChronologicalApproxIndep_of_exactChance
#print axioms figureOnePostInitialDirectFailureBoundFor_of_finiteDeviationExactChance
#print axioms figureOnePostInitialDirectFailureBoundFor_of_mappedProductLe
#print axioms figureOnePostInitialDirectFailureBound_of_chronologicalExactChance

end

end ArlibCommunity.Algorithms.CV18
