/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofDependentSchedule

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-!
# CV18 phase moment and truncation assembly

This file orders the finitely many Figure-1 phases, defines the raw ideal
mean and moment factor in that order, and instantiates the two truncations
from Lemma 7.15 on an abstract executable-history probability space.

The only probabilistic inputs are the executable coordinate's ideal first
moment and its stationary second-moment upper bound.  Lemma 7.14 then supplies
the bias caused by `min (W_j) (alpha * E W_j)`.  The resulting finite-horizon
product estimates are the `hrelative` and `htailSecond` facts required by
Lemma 7.15.  They are intentionally finite-horizon: the earlier unbounded
`forall i` interface is false for positive dependence error.
-/

theorem figureOneIdealPhase_card_eq_phaseCount (q : VolumeParams) :
    Fintype.card (FigureOneIdealPhase q) = figureOneDependentPhaseCount q := by
  have hcomp := Fintype.card_subtype_compl
    (fun k : Fin (terminalPhaseSteps q) => scheduleValue q k ≤ 1)
  have hle := Fintype.card_subtype_le
    (fun k : Fin (terminalPhaseSteps q) => scheduleValue q k ≤ 1)
  rw [figureOneDependentPhaseCount]
  rw [Fintype.card_congr (figureOneIdealPhaseEquiv q)]
  simp only [Fintype.card_sum, Fintype.card_unique]
  simp only [Fintype.card_fin] at hcomp hle
  rw [hcomp]
  omega

noncomputable def figureOneDependentPhaseOrder (q : VolumeParams) :
    Fin (figureOneDependentPhaseCount q) ≃ FigureOneIdealPhase q :=
  Fintype.equivOfCardEq (by simpa using (figureOneIdealPhase_card_eq_phaseCount q).symm)

noncomputable def figureOneDependentPhaseAt (q : VolumeParams) (j : ℕ) : FigureOneIdealPhase q :=
  figureOneDependentPhaseOrder q ⟨j % figureOneDependentPhaseCount q,
    Nat.mod_lt _ (figureOneDependentPhaseCount_pos q)⟩

noncomputable def figureOneDependentRawMean (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  figureOneIdealPhaseMean q I (figureOneDependentPhaseAt q (j - 1))

noncomputable def figureOneDependentMomentFactor (q : VolumeParams) (j : ℕ) : ℝ :=
  figureOneIdealPhaseFactor q (figureOneDependentPhaseAt q (j - 1))

theorem figureOneDependentRawMean_product (q : VolumeParams) (I : VolumeInput q.n) :
    dependentPhaseMeanProduct (figureOneDependentRawMean q I) (figureOneDependentPhaseCount q) =
      ∏ i, figureOneIdealPhaseMean q I i := by
  rw [dependentPhaseMeanProduct]
  calc
    (∏ j ∈ Finset.range (figureOneDependentPhaseCount q), figureOneDependentRawMean q I (j + 1)) =
        ∏ j ∈ Finset.range (figureOneDependentPhaseCount q),
          figureOneIdealPhaseMean q I (figureOneDependentPhaseAt q j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [figureOneDependentRawMean, Nat.add_sub_cancel]
    _ = ∏ i : Fin (figureOneDependentPhaseCount q),
          figureOneIdealPhaseMean q I (figureOneDependentPhaseOrder q i) := by
      rw [← Fin.prod_univ_eq_prod_range
        (fun j => figureOneIdealPhaseMean q I (figureOneDependentPhaseAt q j))]
      apply Fintype.prod_congr
      intro i
      simp only [figureOneDependentPhaseAt, Nat.mod_eq_of_lt i.isLt]
    _ = ∏ i, figureOneIdealPhaseMean q I i :=
      (figureOneDependentPhaseOrder q).prod_comp (figureOneIdealPhaseMean q I)

theorem figureOneDependentMomentFactor_product (q : VolumeParams) :
    dependentPhaseMeanProduct (figureOneDependentMomentFactor q) (figureOneDependentPhaseCount q) =
      ∏ i, figureOneIdealPhaseFactor q i := by
  rw [dependentPhaseMeanProduct]
  calc
    (∏ j ∈ Finset.range (figureOneDependentPhaseCount q), figureOneDependentMomentFactor q (j + 1)) =
        ∏ j ∈ Finset.range (figureOneDependentPhaseCount q),
          figureOneIdealPhaseFactor q (figureOneDependentPhaseAt q j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [figureOneDependentMomentFactor, Nat.add_sub_cancel]
    _ = ∏ i : Fin (figureOneDependentPhaseCount q),
          figureOneIdealPhaseFactor q (figureOneDependentPhaseOrder q i) := by
      rw [← Fin.prod_univ_eq_prod_range
        (fun j => figureOneIdealPhaseFactor q (figureOneDependentPhaseAt q j))]
      apply Fintype.prod_congr
      intro i
      simp only [figureOneDependentPhaseAt, Nat.mod_eq_of_lt i.isLt]
    _ = ∏ i, figureOneIdealPhaseFactor q i :=
      (figureOneDependentPhaseOrder q).prod_comp (figureOneIdealPhaseFactor q)

theorem figureOneDependentRawMean_pos (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) :
    0 < figureOneDependentRawMean q I j :=
  figureOneIdealPhaseMean_pos q I _

theorem figureOneDependentMomentFactor_one_le (q : VolumeParams) (j : ℕ) :
    1 ≤ figureOneDependentMomentFactor q j :=
  figureOneIdealPhaseFactor_one_le q _

theorem figureOneDependentMomentFactor_product_le (q : VolumeParams) :
    dependentPhaseMeanProduct (figureOneDependentMomentFactor q) (figureOneDependentPhaseCount q) ≤
      Real.exp (13 * q.eps ^ 2 / 512) := by
  rw [figureOneDependentMomentFactor_product]
  exact figureOneIdealPhaseFactor_product_le q

theorem figureOneIdealPhaseFactor_le_two (q : VolumeParams) (i : FigureOneIdealPhase q) :
    figureOneIdealPhaseFactor q i ≤ 2 := by
  cases i with
  | fixed k =>
      simp only [figureOneIdealPhaseFactor]
      have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
      have hc : (1 : ℝ) ≤ figureOneFixedSampleCount q := by
        exact_mod_cast figureOneFixedSampleCount_pos q
      have hn0 : (0 : ℝ) < q.n := by linarith
      have hc0 : (0 : ℝ) < figureOneFixedSampleCount q := by linarith
      rw [div_div]
      have hden : (3 : ℝ) ≤ (q.n : ℝ) * figureOneFixedSampleCount q := by
        nlinarith [mul_le_mul hn hc (by norm_num) hn0.le]
      have hfrac : (2 : ℝ) / ((q.n : ℝ) * figureOneFixedSampleCount q) ≤ 2 / 3 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
      linarith
  | accelerated k =>
      simp only [figureOneIdealPhaseFactor]
      have hsT : scheduleValue q k ≤ terminalVariance q :=
        scheduleValue_le_terminal q k
      have hT : 0 < terminalVariance q := terminalVariance_pos' q
      have hc : (1 : ℝ) ≤ figureOneSampleCount q := by
        exact_mod_cast figureOneSampleCount_pos q
      have hc0 : (0 : ℝ) < figureOneSampleCount q := by linarith
      have hratio : scheduleValue q k / terminalVariance q ≤ 1 := by
        exact (div_le_one hT).2 hsT
      have hfrac : scheduleValue q k / terminalVariance q /
          figureOneSampleCount q ≤ 1 := by
        apply (div_le_one hc0).2
        exact hratio.trans hc
      linarith
  | terminal =>
      simp only [figureOneIdealPhaseFactor]
      have hc : (1 : ℝ) ≤ figureOneSampleCount q := by
        exact_mod_cast figureOneSampleCount_pos q
      have hc0 : (0 : ℝ) < figureOneSampleCount q := by linarith
      have hexp : Real.exp (1 / 2) ≤ (5 / 3 : ℝ) := by
        convert Real.exp_le_two_add_div_two_sub (x := (1 / 2 : ℝ))
          (by norm_num) (by norm_num) using 1 <;> norm_num
      have hfrac : (Real.exp (1 / 2) - 1) /
          figureOneSampleCount q ≤ 2 / 3 := by
        apply (div_le_iff₀ hc0).2
        nlinarith
      linarith

theorem figureOneDependentAlpha_ge_1024 (q : VolumeParams) :
    (1024 : ℝ) ≤ figureOneDependentAlpha q := by
  have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  rw [figureOneDependentAlpha, le_div_iff₀ (sq_pos_of_pos q.heps.1)]
  nlinarith

noncomputable def figureOneHistoryTruncatedPhase {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (W : ℕ → Omega → ℝ) :
    ℕ → Omega → ℝ :=
  dependentTruncatedPhase (figureOneDependentAlpha q) (figureOneDependentRawMean q I) W

noncomputable def figureOneHistoryTruncatedMean {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    (W : ℕ → Omega → ℝ) (j : ℕ) : ℝ :=
  ∫ omega, figureOneHistoryTruncatedPhase q I W j omega ∂mu

noncomputable def figureOneHistoryTruncatedSecond {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    (W : ℕ → Omega → ℝ) (j : ℕ) : ℝ :=
  ∫ omega, figureOneHistoryTruncatedPhase q I W j omega ^ 2 ∂mu

theorem figureOneHistoryTruncatedPhase_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (W : ℕ → Omega → ℝ)
    (j : ℕ) (omega : Omega) :
    figureOneHistoryTruncatedPhase q I W j omega =
      dependentTruncatedPhase (figureOneDependentAlpha q)
        (figureOneDependentRawMean q I) W j omega := rfl

theorem figureOneHistoryTruncatedMean_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    (W : ℕ → Omega → ℝ) (j : ℕ) :
    (∫ omega, figureOneHistoryTruncatedPhase q I W j omega ∂mu) =
      figureOneHistoryTruncatedMean q I mu W j := rfl

theorem figureOneHistoryTruncatedSecond_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    (W : ℕ → Omega → ℝ) (j : ℕ) :
    (∫ omega, figureOneHistoryTruncatedPhase q I W j omega ^ 2 ∂mu) =
      figureOneHistoryTruncatedSecond q I mu W j := rfl

theorem figureOneHistoryTruncatedPhase_measurable {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j)) (j : ℕ) :
    Measurable (figureOneHistoryTruncatedPhase q I W j) := by
  unfold figureOneHistoryTruncatedPhase dependentTruncatedPhase
  exact (hWmeas j).min measurable_const

theorem figureOneHistoryTruncatedPhase_nonneg {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (W : ℕ → Omega → ℝ)
    (hW0 : ∀ j omega, 0 ≤ W j omega) (j : ℕ) (omega : Omega) :
    0 ≤ figureOneHistoryTruncatedPhase q I W j omega := by
  unfold figureOneHistoryTruncatedPhase dependentTruncatedPhase
  exact le_min (hW0 j omega)
    (mul_nonneg (figureOneDependentAlpha_pos q).le (figureOneDependentRawMean_pos q I j).le)

theorem figureOneHistoryTruncatedPhase_le_cap {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (W : ℕ → Omega → ℝ)
    (j : ℕ) (omega : Omega) :
    figureOneHistoryTruncatedPhase q I W j omega ≤ figureOneDependentAlpha q * figureOneDependentRawMean q I j := by
  unfold figureOneHistoryTruncatedPhase dependentTruncatedPhase
  exact min_le_right _ _

theorem figureOneHistoryTruncatedPhase_le {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (W : ℕ → Omega → ℝ)
    (j : ℕ) (omega : Omega) : figureOneHistoryTruncatedPhase q I W j omega ≤ W j omega := by
  unfold figureOneHistoryTruncatedPhase dependentTruncatedPhase
  exact min_le_left _ _

theorem figureOneHistoryTruncatedPhase_memLp_two {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsFiniteMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega) (j : ℕ) :
    MemLp (figureOneHistoryTruncatedPhase q I W j) 2 mu := by
  apply MemLp.of_bound (figureOneHistoryTruncatedPhase_measurable q I W hWmeas j).aestronglyMeasurable
    (figureOneDependentAlpha q * figureOneDependentRawMean q I j)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (figureOneHistoryTruncatedPhase_nonneg q I W hW0 j omega)]
  exact figureOneHistoryTruncatedPhase_le_cap q I W j omega

theorem figureOneHistoryTruncatedMean_sq_le_second {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu] (W : ℕ → Omega → ℝ)
    (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega) (j : ℕ) :
    figureOneHistoryTruncatedMean q I mu W j ^ 2 ≤ figureOneHistoryTruncatedSecond q I mu W j := by
  have hmem := figureOneHistoryTruncatedPhase_memLp_two q I mu W hWmeas hW0 j
  have hdev : 0 ≤ ∫ omega,
      (figureOneHistoryTruncatedPhase q I W j omega - figureOneHistoryTruncatedMean q I mu W j) ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  rw [integral_sub_const_sq_eq mu hmem (figureOneHistoryTruncatedMean q I mu W j)] at hdev
  dsimp only [figureOneHistoryTruncatedMean, figureOneHistoryTruncatedSecond] at hdev ⊢
  nlinarith

theorem figureOneHistoryTruncatedSecond_nonneg {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    (W : ℕ → Omega → ℝ) (j : ℕ) :
    0 ≤ figureOneHistoryTruncatedSecond q I mu W j := by
  exact integral_nonneg fun _ => sq_nonneg _

theorem figureOneHistoryTruncatedSecond_le_factor_mul_rawMean_sq
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsFiniteMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) (j : ℕ) :
    figureOneHistoryTruncatedSecond q I mu W j ≤ figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2 := by
  have hVmem := figureOneHistoryTruncatedPhase_memLp_two q I mu W hWmeas hW0 j
  have hle : figureOneHistoryTruncatedSecond q I mu W j ≤ ∫ omega, W j omega ^ 2 ∂mu := by
    dsimp only [figureOneHistoryTruncatedSecond]
    apply integral_mono hVmem.integrable_sq (hWmem j).integrable_sq
    intro omega
    exact (sq_le_sq₀ (figureOneHistoryTruncatedPhase_nonneg q I W hW0 j omega)
      (hW0 j omega)).2 (figureOneHistoryTruncatedPhase_le q I W j omega)
  exact hle.trans (hWsecond j)

theorem figureOneHistoryTruncatedMean_ge_three_quarters_rawMean
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) (j : ℕ) :
    (3 / 4 : ℝ) * figureOneDependentRawMean q I j ≤ figureOneHistoryTruncatedMean q I mu W j := by
  let raw := figureOneDependentRawMean q I j
  let alpha := figureOneDependentAlpha q
  have hraw : 0 < raw := figureOneDependentRawMean_pos q I j
  have halpha : (1024 : ℝ) ≤ alpha := figureOneDependentAlpha_ge_1024 q
  have hcap : 0 < alpha * raw := mul_pos (by linarith) hraw
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    ((hWmem j).integrable (by norm_num)) (hWmem j).integrable_sq (hW0 j) hcap
  have hfactor := figureOneIdealPhaseFactor_le_two q (figureOneDependentPhaseAt q (j - 1))
  have hsecond : (∫ omega, W j omega ^ 2 ∂mu) ≤ 2 * raw ^ 2 := by
    exact (hWsecond j).trans (mul_le_mul_of_nonneg_right hfactor (sq_nonneg raw))
  have hloss : (∫ omega, W j omega ^ 2 ∂mu) / (4 * (alpha * raw)) ≤ raw / 2048 := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hcap)]
    have hscaled := mul_le_mul_of_nonneg_right halpha hraw.le
    nlinarith [hsecond]
  dsimp only [figureOneHistoryTruncatedMean, figureOneHistoryTruncatedPhase]
  unfold dependentTruncatedPhase
  rw [hWmean j] at htrunc
  change (3 / 4 : ℝ) * raw ≤ _
  nlinarith

theorem figureOneRawMean_le_one_add_inv_alpha_mul_truncatedMean
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) (j : ℕ) :
    figureOneDependentRawMean q I j ≤ (1 + 1 / figureOneDependentAlpha q) *
      figureOneHistoryTruncatedMean q I mu W j := by
  let raw := figureOneDependentRawMean q I j
  let alpha := figureOneDependentAlpha q
  have hraw : 0 < raw := figureOneDependentRawMean_pos q I j
  have halpha : (1024 : ℝ) ≤ alpha := figureOneDependentAlpha_ge_1024 q
  have hcap : 0 < alpha * raw := mul_pos (by linarith) hraw
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    ((hWmem j).integrable (by norm_num)) (hWmem j).integrable_sq (hW0 j) hcap
  have hfactor := figureOneIdealPhaseFactor_le_two q (figureOneDependentPhaseAt q (j - 1))
  have hsecond : (∫ omega, W j omega ^ 2 ∂mu) ≤ 2 * raw ^ 2 := by
    exact (hWsecond j).trans (mul_le_mul_of_nonneg_right hfactor (sq_nonneg raw))
  have hloss : (∫ omega, W j omega ^ 2 ∂mu) / (4 * (alpha * raw)) ≤
      raw / (2 * alpha) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hcap)]
    field_simp [show alpha ≠ 0 by linarith]
    nlinarith [hsecond]
  have hmeanLower : (1 - 1 / (2 * alpha)) * raw ≤ figureOneHistoryTruncatedMean q I mu W j := by
    rw [hWmean j] at htrunc
    change (∫ omega, min (W j omega) (alpha * raw) ∂mu) ≥
      raw - (∫ omega, W j omega ^ 2 ∂mu) / (4 * (alpha * raw)) at htrunc
    change (1 - 1 / (2 * alpha)) * raw ≤
      ∫ omega, min (W j omega) (alpha * raw) ∂mu
    calc
      (1 - 1 / (2 * alpha)) * raw = raw - raw / (2 * alpha) := by ring
      _ ≤ raw - (∫ omega, W j omega ^ 2 ∂mu) / (4 * (alpha * raw)) :=
        sub_le_sub_left hloss raw
      _ ≤ _ := htrunc
  have hinv0 : 0 ≤ 1 / alpha := by positivity
  have hinv1 : 1 / alpha ≤ 1 := by
    exact (div_le_one (by linarith : 0 < alpha)).2 (by linarith)
  have hcoefficient : 1 ≤
      (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) := by
    rw [show (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) =
      1 + (1 / alpha) * (1 - 1 / alpha) / 2 by ring]
    nlinarith [mul_nonneg hinv0 (sub_nonneg.mpr hinv1)]
  have hscale := mul_le_mul_of_nonneg_left hmeanLower
    (by positivity : 0 ≤ 1 + 1 / alpha)
  change raw ≤ (1 + 1 / alpha) * figureOneHistoryTruncatedMean q I mu W j
  calc
    raw = 1 * raw := by ring
    _ ≤ ((1 + 1 / alpha) * (1 - 1 / (2 * alpha))) * raw :=
      mul_le_mul_of_nonneg_right hcoefficient hraw.le
    _ = (1 + 1 / alpha) * ((1 - 1 / (2 * alpha)) * raw) := by ring
    _ ≤ (1 + 1 / alpha) * figureOneHistoryTruncatedMean q I mu W j := hscale

theorem figureOneHistoryTruncatedMean_pos
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) (j : ℕ) :
    0 < figureOneHistoryTruncatedMean q I mu W j := by
  exact lt_of_lt_of_le
    (mul_pos (by norm_num) (figureOneDependentRawMean_pos q I j))
    (figureOneHistoryTruncatedMean_ge_three_quarters_rawMean q I mu W hWmeas hW0 hWmem
      hWmean hWsecond j)

theorem figureOneHistoryTruncatedMean_le_rawMean
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneDependentRawMean q I j) (j : ℕ) :
    figureOneHistoryTruncatedMean q I mu W j ≤
      figureOneDependentRawMean q I j := by
  rw [← hWmean j]
  dsimp only [figureOneHistoryTruncatedMean]
  apply integral_mono
    ((figureOneHistoryTruncatedPhase_memLp_two q I mu W hWmeas hW0 j).integrable
      (by norm_num))
    ((hWmem j).integrable (by norm_num))
  exact figureOneHistoryTruncatedPhase_le q I W j

theorem figureOneRawMean_le_two_truncatedMean
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) (j : ℕ) :
    figureOneDependentRawMean q I j ≤ 2 * figureOneHistoryTruncatedMean q I mu W j := by
  have h := figureOneHistoryTruncatedMean_ge_three_quarters_rawMean q I mu W hWmeas hW0
    hWmem hWmean hWsecond j
  nlinarith [figureOneDependentRawMean_pos q I j]

theorem figureOneRawMean_sq_le_two_truncatedSecond
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) (j : ℕ) :
    figureOneDependentRawMean q I j ^ 2 ≤ 2 * figureOneHistoryTruncatedSecond q I mu W j := by
  have hmeanLower := figureOneHistoryTruncatedMean_ge_three_quarters_rawMean q I mu W hWmeas hW0
    hWmem hWmean hWsecond j
  have hmean0 := (figureOneHistoryTruncatedMean_pos q I mu W hWmeas hW0 hWmem hWmean hWsecond j).le
  have hsquare : ((3 / 4 : ℝ) * figureOneDependentRawMean q I j) ^ 2 ≤
      figureOneHistoryTruncatedMean q I mu W j ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) (figureOneDependentRawMean_pos q I j).le) hmean0).2
      hmeanLower
  have hmoment := figureOneHistoryTruncatedMean_sq_le_second q I mu W hWmeas hW0 j
  nlinarith [sq_nonneg (figureOneDependentRawMean q I j)]

theorem figureOneRawMeanProduct_le_pow_mul_truncatedMeanProduct
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) (i : ℕ) :
    dependentPhaseMeanProduct (figureOneDependentRawMean q I) i ≤
      (1 + 1 / figureOneDependentAlpha q) ^ i *
        dependentPhaseMeanProduct (figureOneHistoryTruncatedMean q I mu W) i := by
  unfold dependentPhaseMeanProduct
  calc
    (∏ j ∈ Finset.range i, figureOneDependentRawMean q I (j + 1)) ≤
        ∏ j ∈ Finset.range i,
          ((1 + 1 / figureOneDependentAlpha q) *
            figureOneHistoryTruncatedMean q I mu W (j + 1)) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact (figureOneDependentRawMean_pos q I (j + 1)).le
      · intro j hj
        exact figureOneRawMean_le_one_add_inv_alpha_mul_truncatedMean q I mu W hWmeas hW0
          hWmem hWmean hWsecond (j + 1)
    _ = (1 + 1 / figureOneDependentAlpha q) ^ i *
        ∏ j ∈ Finset.range i, figureOneHistoryTruncatedMean q I mu W (j + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

theorem figureOneTruncatedMeanProduct_le_rawMeanProduct
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneDependentRawMean q I j) (i : ℕ) :
    dependentPhaseMeanProduct (figureOneHistoryTruncatedMean q I mu W) i ≤
      dependentPhaseMeanProduct (figureOneDependentRawMean q I) i := by
  unfold dependentPhaseMeanProduct
  apply Finset.prod_le_prod
  · intro j hj
    exact integral_nonneg fun omega =>
      figureOneHistoryTruncatedPhase_nonneg q I W hW0 (j + 1) omega
  · intro j hj
    exact figureOneHistoryTruncatedMean_le_rawMean q I mu W hWmeas hW0 hWmem
      hWmean (j + 1)

theorem figureOne_one_add_inv_alpha_pow_le_exp
    (q : VolumeParams) {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    (1 + 1 / figureOneDependentAlpha q) ^ i ≤
      Real.exp (q.eps ^ 2 / 1024) := by
  let alpha := figureOneDependentAlpha q
  have ha : 0 < alpha := figureOneDependentAlpha_pos q
  have hinv0 : 0 ≤ 1 / alpha := by positivity
  have hbase : 1 + 1 / alpha ≤ Real.exp (1 / alpha) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / alpha)
  have hpow : (1 + 1 / alpha) ^ i ≤ Real.exp (1 / alpha) ^ i :=
    pow_le_pow_left₀ (by positivity) hbase i
  rw [← Real.exp_nat_mul] at hpow
  have hiR : (i : ℝ) ≤ figureOneDependentPhaseCount q := by exact_mod_cast hi
  have hquot : (i : ℝ) / alpha ≤
      (figureOneDependentPhaseCount q : ℝ) / alpha :=
    div_le_div_of_nonneg_right hiR ha.le
  have hexp : Real.exp ((i : ℝ) / alpha) ≤
      Real.exp (q.eps ^ 2 / 1024) := by
    apply Real.exp_le_exp.mpr
    simpa [alpha, figureOneDependentPhaseCount_div_alpha q] using hquot
  change (1 + 1 / alpha) ^ i ≤ _
  calc
    _ ≤ Real.exp ((i : ℝ) * (1 / alpha)) := hpow
    _ = Real.exp ((i : ℝ) / alpha) := by congr 1; ring
    _ ≤ _ := hexp

theorem figureOneTruncatedSecondProduct_le_factor_mul_rawMeanProduct_sq
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) (i : ℕ) :
    dependentPhaseMeanProduct (figureOneHistoryTruncatedSecond q I mu W) i ≤
      dependentPhaseMeanProduct (figureOneDependentMomentFactor q) i *
        dependentPhaseMeanProduct (figureOneDependentRawMean q I) i ^ 2 := by
  unfold dependentPhaseMeanProduct
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro j hj
    exact figureOneHistoryTruncatedSecond_nonneg q I mu W (j + 1)
  · intro j hj
    exact figureOneHistoryTruncatedSecond_le_factor_mul_rawMean_sq q I mu W hWmeas hW0 hWmem
      hWsecond (j + 1)

theorem figureOneMomentFactor_partialProduct_le_exp
    (q : VolumeParams) {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct (figureOneDependentMomentFactor q) i ≤
      Real.exp (13 * q.eps ^ 2 / 512) := by
  have hmono := Finset.prod_mono_set_of_one_le
    (f := fun j => figureOneDependentMomentFactor q (j + 1))
    (fun j => figureOneDependentMomentFactor_one_le q (j + 1))
    (Finset.range_mono hi)
  unfold dependentPhaseMeanProduct
  exact hmono.trans (figureOneDependentMomentFactor_product_le q)

theorem figureOne_exp_seven_eps_sq_div_256_le (q : VolumeParams) :
    Real.exp (7 * q.eps ^ 2 / 256) ≤ 1 + q.eps ^ 2 / 32 := by
  let y := q.eps ^ 2
  let x := 7 * y / 256
  have hy0 : 0 ≤ y := sq_nonneg q.eps
  have hy1 : y ≤ 1 := by
    dsimp [y]
    nlinarith [q.heps.1, q.heps.2]
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x < 2 := by dsimp [x]; nlinarith
  have hexp : Real.exp x ≤ (2 + x) / (2 - x) :=
    Real.exp_le_two_add_div_two_sub hx0 hx2
  have hrational : (2 + x) / (2 - x) ≤ 1 + y / 32 := by
    rw [div_le_iff₀ (sub_pos.mpr hx2)]
    dsimp [x]
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  change Real.exp x ≤ 1 + y / 32
  exact hexp.trans hrational

theorem figureOne_exp_eps_sq_div_1024_le (q : VolumeParams) :
    Real.exp (q.eps ^ 2 / 1024) ≤ 1 + q.eps ^ 2 / 512 := by
  let y := q.eps ^ 2
  let x := y / 1024
  have hy0 : 0 ≤ y := sq_nonneg q.eps
  have hy1 : y ≤ 1 := by
    dsimp [y]
    nlinarith [q.heps.1, q.heps.2]
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x < 2 := by dsimp [x]; nlinarith
  have hexp : Real.exp x ≤ (2 + x) / (2 - x) :=
    Real.exp_le_two_add_div_two_sub hx0 hx2
  have hrational : (2 + x) / (2 - x) ≤ 1 + y / 512 := by
    rw [div_le_iff₀ (sub_pos.mpr hx2)]
    dsimp [x]
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  change Real.exp x ≤ 1 + y / 512
  exact hexp.trans hrational

/-- Lemma 7.14's missing center transfer: the product of truncated phase
means is close to, but generally not equal to, the telescoping ideal mean. -/
theorem figureOneHistoryTruncatedMeanProduct_relativeApprox_ideal
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) =
      figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j *
        figureOneDependentRawMean q I j ^ 2) :
    RelativeApprox (q.eps / 32)
      (∏ i, figureOneIdealPhaseMean q I i)
      (dependentPhaseMeanProduct (figureOneHistoryTruncatedMean q I mu W)
        (figureOneDependentPhaseCount q)) := by
  rw [← figureOneDependentRawMean_product q I]
  let raw := dependentPhaseMeanProduct (figureOneDependentRawMean q I)
    (figureOneDependentPhaseCount q)
  let truncated := dependentPhaseMeanProduct
    (figureOneHistoryTruncatedMean q I mu W) (figureOneDependentPhaseCount q)
  have hrawPos : 0 < raw := by
    dsimp [raw, dependentPhaseMeanProduct]
    apply Finset.prod_pos
    intro j hj
    exact figureOneDependentRawMean_pos q I (j + 1)
  have htruncated0 : 0 ≤ truncated :=
    dependentPhaseMeanProduct_nonneg _
      (fun j => integral_nonneg fun omega =>
        figureOneHistoryTruncatedPhase_nonneg q I W hW0 j omega) _
  have htruncated_le : truncated ≤ raw :=
    figureOneTruncatedMeanProduct_le_rawMeanProduct q I mu W hWmeas hW0
      hWmem hWmean _
  have hrawPow := figureOneRawMeanProduct_le_pow_mul_truncatedMeanProduct
    q I mu W hWmeas hW0 hWmem hWmean hWsecond
      (figureOneDependentPhaseCount q)
  have hpow := figureOne_one_add_inv_alpha_pow_le_exp q (le_refl _)
  have hrawExp : raw ≤ Real.exp (q.eps ^ 2 / 1024) * truncated := by
    exact hrawPow.trans (mul_le_mul_of_nonneg_right hpow htruncated0)
  have hrawBound : raw ≤ (1 + q.eps ^ 2 / 512) * truncated :=
    hrawExp.trans (mul_le_mul_of_nonneg_right
      (figureOne_exp_eps_sq_div_1024_le q) htruncated0)
  have hepsSq : q.eps ^ 2 ≤ q.eps := by
    nlinarith [q.heps.1, q.heps.2]
  have hcoefficient :
      (1 + q.eps ^ 2 / 512) * (1 - q.eps / 32) ≤ 1 := by
    nlinarith [mul_nonneg q.heps.1.le
      (sub_nonneg.mpr (by linarith [q.heps.2] : q.eps ≤ 32))]
  unfold RelativeApprox Arlib.relErr
  change (1 - q.eps / 32) * raw ≤ truncated ∧
    truncated ≤ (1 + q.eps / 32) * raw
  constructor
  · have hscaled : (1 + q.eps ^ 2 / 512) *
        ((1 - q.eps / 32) * raw) ≤
      (1 + q.eps ^ 2 / 512) * truncated := by
      calc
        _ = ((1 + q.eps ^ 2 / 512) * (1 - q.eps / 32)) * raw := by ring
        _ ≤ 1 * raw := mul_le_mul_of_nonneg_right hcoefficient hrawPos.le
        _ = raw := one_mul _
        _ ≤ _ := hrawBound
    exact le_of_mul_le_mul_left hscaled (by positivity)
  · calc
      truncated ≤ raw := htruncated_le
      _ ≤ (1 + q.eps / 32) * raw := by
        nlinarith [hrawPos, q.heps.1]

theorem figureOneTruncatedSecondProduct_le_one_add_eps_sq_div_32
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct (figureOneHistoryTruncatedSecond q I mu W) i ≤
      (1 + q.eps ^ 2 / 32) *
        dependentPhaseMeanProduct (figureOneHistoryTruncatedMean q I mu W) i ^ 2 := by
  let meanProduct := dependentPhaseMeanProduct (figureOneHistoryTruncatedMean q I mu W) i
  let rawProduct := dependentPhaseMeanProduct (figureOneDependentRawMean q I) i
  let factorProduct := dependentPhaseMeanProduct (figureOneDependentMomentFactor q) i
  have hmean0 : 0 ≤ meanProduct :=
    dependentPhaseMeanProduct_nonneg _
      (fun j => (figureOneHistoryTruncatedMean_pos q I mu W hWmeas hW0 hWmem hWmean hWsecond j).le) i
  have hraw0 : 0 ≤ rawProduct :=
    dependentPhaseMeanProduct_nonneg _ (fun j => (figureOneDependentRawMean_pos q I j).le) i
  have hfactor0 : 0 ≤ factorProduct :=
    dependentPhaseMeanProduct_nonneg _
      (fun j => zero_le_one.trans (figureOneDependentMomentFactor_one_le q j)) i
  have hraw := figureOneRawMeanProduct_le_pow_mul_truncatedMeanProduct q I mu W hWmeas
    hW0 hWmem hWmean hWsecond i
  have hpow := figureOne_one_add_inv_alpha_pow_le_exp q hi
  have hrawExp : rawProduct ≤ Real.exp (q.eps ^ 2 / 1024) * meanProduct := by
    exact hraw.trans (mul_le_mul_of_nonneg_right hpow hmean0)
  have hrawSq : rawProduct ^ 2 ≤
      Real.exp (q.eps ^ 2 / 1024) ^ 2 * meanProduct ^ 2 := by
    have := (sq_le_sq₀ hraw0
      (mul_nonneg (Real.exp_pos _).le hmean0)).2 hrawExp
    nlinarith
  have hsecond := figureOneTruncatedSecondProduct_le_factor_mul_rawMeanProduct_sq
    q I mu W hWmeas hW0 hWmem hWsecond i
  have hfactor := figureOneMomentFactor_partialProduct_le_exp q hi
  have hbound : factorProduct * rawProduct ^ 2 ≤
      Real.exp (13 * q.eps ^ 2 / 512) *
        (Real.exp (q.eps ^ 2 / 1024) ^ 2 * meanProduct ^ 2) := by
    exact mul_le_mul hfactor hrawSq (sq_nonneg rawProduct)
      (Real.exp_pos _).le
  have hexpIdentity :
      Real.exp (13 * q.eps ^ 2 / 512) *
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
    dependentPhaseMeanProduct (figureOneHistoryTruncatedSecond q I mu W) i ≤
        factorProduct * rawProduct ^ 2 := hsecond
    _ ≤ Real.exp (13 * q.eps ^ 2 / 512) *
        (Real.exp (q.eps ^ 2 / 1024) ^ 2 * meanProduct ^ 2) := hbound
    _ = Real.exp (7 * q.eps ^ 2 / 256) * meanProduct ^ 2 := by
      rw [← mul_assoc, hexpIdentity]
    _ ≤ (1 + q.eps ^ 2 / 32) * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right (figureOne_exp_seven_eps_sq_div_256_le q)
        (sq_nonneg meanProduct)

theorem figureOneDependentMomentMultiplier_le
    (q : VolumeParams) {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    1 + 2 * figureOneDependentEpsilon q * figureOneDependentAlpha q ^ 4 * i ≤
      1 + q.eps ^ 2 / 2048 := by
  have ha := figureOneDependentAlpha_pos q
  have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have hiR : (i : ℝ) ≤ figureOneDependentPhaseCount q := by exact_mod_cast hi
  rw [figureOneDependentEpsilon]
  field_simp [ha.ne', hm.ne']
  nlinarith

theorem figureOneDependentMomentBudget_le (q : VolumeParams) :
    (1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32) ≤
      1 + q.eps ^ 2 / 16 := by
  have hy0 : 0 ≤ q.eps ^ 2 := sq_nonneg q.eps
  have hy1 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]

theorem figureOneHistory_tailSecond
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) :
    (1 + 2 * figureOneDependentEpsilon q * figureOneDependentAlpha q ^ 4 *
        figureOneDependentPhaseCount q) *
        dependentPhaseMeanProduct (figureOneHistoryTruncatedSecond q I mu W)
          (figureOneDependentPhaseCount q) ≤
      (1 + q.eps ^ 2 / 16) *
        dependentPhaseMeanProduct (figureOneHistoryTruncatedMean q I mu W)
          (figureOneDependentPhaseCount q) ^ 2 := by
  let meanProduct := dependentPhaseMeanProduct (figureOneHistoryTruncatedMean q I mu W)
    (figureOneDependentPhaseCount q)
  have hmeanSq0 : 0 ≤ meanProduct ^ 2 := sq_nonneg _
  have hsecond := figureOneTruncatedSecondProduct_le_one_add_eps_sq_div_32 q I mu W hWmeas
    hW0 hWmem hWmean hWsecond (le_refl _)
  have hmult := figureOneDependentMomentMultiplier_le q (le_refl _)
  have hmult0 : 0 ≤ 1 + 2 * figureOneDependentEpsilon q *
      figureOneDependentAlpha q ^ 4 * (figureOneDependentPhaseCount q : ℝ) := by
    have hterm : 0 ≤ 2 * figureOneDependentEpsilon q *
        figureOneDependentAlpha q ^ 4 * (figureOneDependentPhaseCount q : ℝ) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (figureOneDependentEpsilon_nonneg q))
          (by positivity)) (by positivity)
    linarith
  calc
    _ ≤ (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * figureOneDependentPhaseCount q) *
        ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
      mul_le_mul_of_nonneg_left hsecond hmult0
    _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
        meanProduct ^ 2 := by
      have hscaled := mul_le_mul_of_nonneg_right hmult
        (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
      nlinarith
    _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right (figureOneDependentMomentBudget_le q) hmeanSq0

theorem figureOneHistory_relativeProduct_finite
    {Omega : Type*} [MeasurableSpace Omega]
    (q : VolumeParams) (I : VolumeInput q.n) (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (W : ℕ → Omega → ℝ) (hWmeas : ∀ j, Measurable (W j))
    (hW0 : ∀ j omega, 0 ≤ W j omega)
    (hWmem : ∀ j, MemLp (W j) 2 mu)
    (hWmean : ∀ j, (∫ omega, W j omega ∂mu) = figureOneDependentRawMean q I j)
    (hWsecond : ∀ j, (∫ omega, W j omega ^ 2 ∂mu) ≤
      figureOneDependentMomentFactor q j * figureOneDependentRawMean q I j ^ 2) :
    ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct (figureOneHistoryTruncatedSecond q I mu W) i ≤
        2 * dependentPhaseMeanProduct (figureOneHistoryTruncatedMean q I mu W) i ^ 2 := by
  intro i hi
  let meanProduct := dependentPhaseMeanProduct (figureOneHistoryTruncatedMean q I mu W) i
  have hmeanSq0 : 0 ≤ meanProduct ^ 2 := sq_nonneg _
  have hsecond := figureOneTruncatedSecondProduct_le_one_add_eps_sq_div_32 q I mu W hWmeas
    hW0 hWmem hWmean hWsecond hi
  have hmult := figureOneDependentMomentMultiplier_le q hi
  have hmult0 : 0 ≤ 1 + 2 * figureOneDependentEpsilon q *
      figureOneDependentAlpha q ^ 4 * (i : ℝ) := by
    have hterm : 0 ≤ 2 * figureOneDependentEpsilon q *
        figureOneDependentAlpha q ^ 4 * (i : ℝ) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (figureOneDependentEpsilon_nonneg q))
          (by positivity)) (by positivity)
    linarith
  calc
    _ ≤ (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
        ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
      mul_le_mul_of_nonneg_left hsecond hmult0
    _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
        meanProduct ^ 2 := by
      have hscaled := mul_le_mul_of_nonneg_right hmult
        (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
      nlinarith
    _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
      mul_le_mul_of_nonneg_right (figureOneDependentMomentBudget_le q) hmeanSq0
    _ ≤ 2 * meanProduct ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hmeanSq0
      nlinarith [q.heps.1, q.heps.2]

#print axioms figureOneIdealPhase_card_eq_phaseCount
#print axioms figureOneDependentRawMean_product
#print axioms figureOneDependentMomentFactor_product
#print axioms figureOneHistoryTruncatedMean_ge_three_quarters_rawMean
#print axioms figureOneRawMean_le_one_add_inv_alpha_mul_truncatedMean
#print axioms figureOneTruncatedSecondProduct_le_one_add_eps_sq_div_32
#print axioms figureOneHistoryTruncatedMeanProduct_relativeApprox_ideal
#print axioms figureOneHistory_tailSecond
#print axioms figureOneHistory_relativeProduct_finite

end
end ArlibCommunity.Algorithms.CV18
