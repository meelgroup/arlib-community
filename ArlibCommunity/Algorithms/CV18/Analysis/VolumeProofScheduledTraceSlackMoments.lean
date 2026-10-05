/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceLemma717Capstone

/-!
# Slack moment interface for the executable scheduled trace

The paper's product calculation does not require the finite walk to attain
the ideal IID second-moment factor phase by phase.  A coarse local factor
`2` controls truncation bias, while the sharp information can be supplied as
one finite-prefix product bound.  This is the form naturally produced by a
paired/Markov phase analysis with small explicit slack.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The truncation-loss estimate only uses the coarse bound
`E[W²] ≤ 2 E[W]²`; it does not require the exact ideal phase factor. -/
theorem scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean_of_two
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hrawPos : 0 < scheduledFigureOneTraceRawMean q I j)
    (hWmem : MemLp (scheduledBalancedTracePhaseVariable q j) 2
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)))
    (hsecond :
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2) :
    scheduledFigureOneTraceRawMean q I j ≤
      (1 + 1 / figureOneDependentAlpha q) *
        scheduledFigureOneTraceTruncatedMean q I j := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let raw := scheduledFigureOneTraceRawMean q I j
  let alpha := figureOneDependentAlpha q
  let W := scheduledBalancedTracePhaseVariable q j
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  have halpha : (1024 : ℝ) ≤ alpha := figureOneDependentAlpha_ge_1024 q
  have hcap : 0 < alpha * raw := mul_pos (by linarith) hrawPos
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    (hWmem.integrable (by norm_num)) hWmem.integrable_sq
    (scheduledBalancedTracePhaseVariable_nonnegative q j) hcap
  have hloss : (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) ≤
      raw / (2 * alpha) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hcap)]
    field_simp [show alpha ≠ 0 by linarith]
    nlinarith [hsecond]
  have hmeanLower : (1 - 1 / (2 * alpha)) * raw ≤
      scheduledFigureOneTraceTruncatedMean q I j := by
    change (∫ trace, min (W trace) (alpha * raw) ∂mu) ≥
      raw - (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) at htrunc
    change (1 - 1 / (2 * alpha)) * raw ≤
      ∫ trace, min (W trace) (alpha * raw) ∂mu
    calc
      (1 - 1 / (2 * alpha)) * raw = raw - raw / (2 * alpha) := by ring
      _ ≤ raw - (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) :=
        sub_le_sub_left hloss raw
      _ ≤ _ := htrunc
  have hinv0 : 0 ≤ 1 / alpha := by positivity
  have hinv1 : 1 / alpha ≤ 1 :=
    (div_le_one (by linarith : 0 < alpha)).2 (by linarith)
  have hcoefficient : 1 ≤
      (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) := by
    rw [show (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) =
      1 + (1 / alpha) * (1 - 1 / alpha) / 2 by ring]
    nlinarith [mul_nonneg hinv0 (sub_nonneg.mpr hinv1)]
  have hscale := mul_le_mul_of_nonneg_left hmeanLower
    (by positivity : 0 ≤ 1 + 1 / alpha)
  change raw ≤ (1 + 1 / alpha) *
    scheduledFigureOneTraceTruncatedMean q I j
  calc
    raw = 1 * raw := by ring
    _ ≤ ((1 + 1 / alpha) * (1 - 1 / (2 * alpha))) * raw :=
      mul_le_mul_of_nonneg_right hcoefficient hrawPos.le
    _ = (1 + 1 / alpha) * ((1 - 1 / (2 * alpha)) * raw) := by ring
    _ ≤ _ := hscale

/-- Finite product form of the coarse truncation-loss estimate. -/
theorem scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct_of_two
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I) i ≤
      (1 + 1 / figureOneDependentAlpha q) ^ i *
        dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i := by
  unfold dependentPhaseMeanProduct
  calc
    (∏ j ∈ Finset.range i, scheduledFigureOneTraceRawMean q I (j + 1)) ≤
        ∏ j ∈ Finset.range i,
          ((1 + 1 / figureOneDependentAlpha q) *
            scheduledFigureOneTraceTruncatedMean q I (j + 1)) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact (scheduledFigureOneTraceRawMean_pos q I (j + 1) (by omega)
          (by have := Finset.mem_range.mp hj; omega)).le
      · intro j hj
        have hjm : j + 1 ≤ figureOneDependentPhaseCount q := by
          have := Finset.mem_range.mp hj
          omega
        exact
          scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean_of_two
            q I (j + 1)
            (scheduledFigureOneTraceRawMean_pos q I (j + 1) (by omega) hjm)
            (memLp_scheduledBalancedForwardTrace_phaseVariable
              q I (j + 1) (by omega) hjm)
            (hsecondTwo (j + 1) (by omega) hjm)
    _ = (1 + 1 / figureOneDependentAlpha q) ^ i *
        ∏ j ∈ Finset.range i,
          scheduledFigureOneTraceTruncatedMean q I (j + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- A phase-factor version of the empirical-average calculation in CV18
Lemma 7.15, Eq. (6).  It keeps the executable phase factors abstract so the
finite-walk collector estimate can include its explicit mixing slack. -/
theorem scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor
    (q : VolumeParams) (I : VolumeInput q.n) (factor : ℕ → ℝ)
    (hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        factor j * scheduledFigureOneTraceRawMean q I j ^ 2)
    {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedSecond q I) i ≤
      dependentPhaseMeanProduct factor i *
        dependentPhaseMeanProduct
          (scheduledFigureOneTraceRawMean q I) i ^ 2 := by
  unfold dependentPhaseMeanProduct
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro j hj
    exact integral_nonneg fun _ => sq_nonneg _
  · intro j hj
    have hjm : j + 1 ≤ figureOneDependentPhaseCount q := by
      have := Finset.mem_range.mp hj
      omega
    exact (scheduledFigureOneTrace_truncatedSecond_le_rawSecond
      q I (j + 1) (hrawPos (j + 1) (by omega) hjm)
      (memLp_scheduledBalancedForwardTrace_phaseVariable
        q I (j + 1) (by omega) hjm)).trans
          (hsecond (j + 1) (by omega) hjm)

/-- The exact finite-prefix budget needed after the phasewise empirical
second-moment estimate.  This isolates the chunk-product arithmetic in the
middle of CV18 Lemma 7.15 from the Markov-chain collector proof. -/
theorem scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor_budget
    (q : VolumeParams) (I : VolumeInput q.n) (factor : ℕ → ℝ)
    (hfactor0 : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 ≤ factor j)
    (hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hsecondFactor : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        factor j * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hbudget : ∀ i, i ≤ figureOneDependentPhaseCount q →
      dependentPhaseMeanProduct factor i *
          ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2 ≤
        1 + q.eps ^ 2 / 32) :
    ∀ i, i ≤ figureOneDependentPhaseCount q →
      dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        (1 + q.eps ^ 2 / 32) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I) i ^ 2 := by
  intro i hi
  let raw := dependentPhaseMeanProduct
    (scheduledFigureOneTraceRawMean q I) i
  let truncated := dependentPhaseMeanProduct
    (scheduledFigureOneTraceTruncatedMean q I) i
  let factorProduct := dependentPhaseMeanProduct factor i
  have hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j :=
    fun j hj1 hjm => scheduledFigureOneTraceRawMean_pos q I j hj1 hjm
  have hfactorProduct0 : 0 ≤ factorProduct := by
    dsimp only [factorProduct, dependentPhaseMeanProduct]
    apply Finset.prod_nonneg
    intro j hj
    exact hfactor0 (j + 1) (by omega) (by
      have := Finset.mem_range.mp hj
      omega)
  have htruncated0 : 0 ≤ truncated :=
    dependentPhaseMeanProduct_nonneg _ (fun j =>
      scheduledFigureOneTraceTruncatedMean_nonnegative q I j <| by
        unfold scheduledFigureOneTraceRawMean
        exact integral_nonneg fun trace =>
          scheduledBalancedTracePhaseVariable_nonnegative q j trace) i
  have hraw0 : 0 ≤ raw :=
    dependentPhaseMeanProduct_nonneg _ (fun j => by
      unfold scheduledFigureOneTraceRawMean
      exact integral_nonneg fun trace =>
        scheduledBalancedTracePhaseVariable_nonnegative q j trace) i
  have hraw :=
    scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct_of_two
      q I hsecondTwo hi
  have hcoefficient0 :
      0 ≤ (1 + 1 / figureOneDependentAlpha q) ^ i := by
    apply pow_nonneg
    have halpha := figureOneDependentAlpha_pos q
    have hinv : 0 ≤ 1 / figureOneDependentAlpha q :=
      (one_div_pos.mpr halpha).le
    linarith
  have hrawSq : raw ^ 2 ≤
      (((1 + 1 / figureOneDependentAlpha q) ^ i) * truncated) ^ 2 :=
    (sq_le_sq₀ hraw0
      (mul_nonneg hcoefficient0 htruncated0)).2 hraw
  have hsecondProduct :=
    scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor
      q I factor hrawPos hsecondFactor hi
  calc
    dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        factorProduct * raw ^ 2 := hsecondProduct
    _ ≤ factorProduct *
        (((1 + 1 / figureOneDependentAlpha q) ^ i) * truncated) ^ 2 :=
      mul_le_mul_of_nonneg_left hrawSq hfactorProduct0
    _ = (factorProduct *
          ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2) *
        truncated ^ 2 := by ring
    _ ≤ (1 + q.eps ^ 2 / 32) * truncated ^ 2 :=
      mul_le_mul_of_nonneg_right (hbudget i hi) (sq_nonneg truncated)

/-! ## An explicit per-phase finite-walk slack budget -/

/-- Multiplicative slack available to the executable collector in each
phase after reserving the paper's ideal moment and truncation budgets. -/
noncomputable def figureOneExecutableMomentSlack (q : VolumeParams) : ℝ :=
  q.eps ^ 2 / (4096 * (figureOneDependentPhaseCount q : ℝ))

/-- The chronological ideal factor enlarged by the available executable
finite-walk slack. -/
noncomputable def figureOneExecutableMomentFactor
    (q : VolumeParams) (j : ℕ) : ℝ :=
  figureOneChronologicalMomentFactor q j *
    (1 + figureOneExecutableMomentSlack q)

theorem figureOneExecutableMomentSlack_nonneg (q : VolumeParams) :
    0 ≤ figureOneExecutableMomentSlack q := by
  unfold figureOneExecutableMomentSlack
  positivity

theorem figureOneIdealPhaseFactor_le_five_thirds
    (q : VolumeParams) (phase : FigureOneIdealPhase q) :
    figureOneIdealPhaseFactor q phase ≤ 5 / 3 := by
  cases phase with
  | fixed k =>
      simp only [figureOneIdealPhaseFactor]
      have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
      have hc : (1 : ℝ) ≤ figureOneFixedSampleCount q := by
        exact_mod_cast figureOneFixedSampleCount_pos q
      have hn0 : (0 : ℝ) < q.n := by linarith
      have hden : (3 : ℝ) ≤
          (q.n : ℝ) * figureOneFixedSampleCount q := by
        nlinarith [mul_le_mul hn hc (by norm_num) hn0.le]
      rw [div_div]
      have hfrac : (2 : ℝ) /
          ((q.n : ℝ) * figureOneFixedSampleCount q) ≤ 2 / 3 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
      linarith
  | accelerated k =>
      simp only [figureOneIdealPhaseFactor]
      have hsT : scheduleValue q k ≤ terminalVariance q :=
        scheduleValue_le_terminal q k
      have hT : 0 < terminalVariance q := terminalVariance_pos' q
      have hH : (1 : ℝ) ≤ protectedLog (terminalVariance q) :=
        le_max_left _ _
      have he2 : q.eps ^ 2 ≤ 1 := by
        nlinarith [q.heps.1, q.heps.2]
      have hlower := figureOneSampleCount_cast_lower q
      have hraw : (512 : ℝ) ≤
          512 * protectedLog (terminalVariance q) / q.eps ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos q.heps.1)]
        nlinarith
      have hc : (512 : ℝ) ≤ figureOneSampleCount q :=
        hraw.trans hlower
      have hc0 : (0 : ℝ) < figureOneSampleCount q := by linarith
      have hratio : scheduleValue q k / terminalVariance q ≤ 1 :=
        (div_le_one hT).2 hsT
      have hfrac : scheduleValue q k / terminalVariance q /
          figureOneSampleCount q ≤ 2 / 3 := by
        apply (div_le_iff₀ hc0).2
        nlinarith
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

theorem figureOneChronologicalMomentFactor_le_five_thirds
    (q : VolumeParams) (j : ℕ) :
    figureOneChronologicalMomentFactor q j ≤ 5 / 3 :=
  figureOneIdealPhaseFactor_le_five_thirds q
    (figureOneChronologicalPhaseAt q j)

theorem figureOneExecutableMomentFactor_nonneg
    (q : VolumeParams) (j : ℕ) :
    0 ≤ figureOneExecutableMomentFactor q j := by
  unfold figureOneExecutableMomentFactor
  exact mul_nonneg
    (zero_le_one.trans (figureOneChronologicalMomentFactor_one_le q j))
    (by linarith [figureOneExecutableMomentSlack_nonneg q])

theorem figureOneExecutableMomentFactor_le_two
    (q : VolumeParams) (j : ℕ) :
    figureOneExecutableMomentFactor q j ≤ 2 := by
  have hm : (1 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have he : q.eps ^ 2 ≤ 1 := by
    nlinarith [q.heps.1, q.heps.2]
  have hslack : figureOneExecutableMomentSlack q ≤ 1 / 4096 := by
    unfold figureOneExecutableMomentSlack
    apply (div_le_iff₀ (by positivity :
      (0 : ℝ) < 4096 * figureOneDependentPhaseCount q)).2
    nlinarith
  unfold figureOneExecutableMomentFactor
  have hchron0 : 0 ≤ figureOneChronologicalMomentFactor q j :=
    zero_le_one.trans (figureOneChronologicalMomentFactor_one_le q j)
  have hslackBase0 : 0 ≤ 1 + figureOneExecutableMomentSlack q := by
    linarith [figureOneExecutableMomentSlack_nonneg q]
  calc
    figureOneChronologicalMomentFactor q j *
        (1 + figureOneExecutableMomentSlack q) ≤
        (5 / 3) * (1 + 1 / 4096) :=
      mul_le_mul (figureOneChronologicalMomentFactor_le_five_thirds q j)
        (by linarith) hslackBase0 (by norm_num)
    _ ≤ 2 := by norm_num

theorem figureOne_one_add_executableMomentSlack_pow_le_exp
    (q : VolumeParams) {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    (1 + figureOneExecutableMomentSlack q) ^ i ≤
      Real.exp (q.eps ^ 2 / 4096) := by
  let delta := figureOneExecutableMomentSlack q
  have hdelta0 : 0 ≤ delta := figureOneExecutableMomentSlack_nonneg q
  have hbase : 1 + delta ≤ Real.exp delta := by
    simpa [add_comm] using Real.add_one_le_exp delta
  have hpow : (1 + delta) ^ i ≤ Real.exp delta ^ i :=
    pow_le_pow_left₀ (by positivity) hbase i
  rw [← Real.exp_nat_mul] at hpow
  have hiR : (i : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast hi
  have hmR : (0 : ℝ) < figureOneDependentPhaseCount q := by
    exact_mod_cast figureOneDependentPhaseCount_pos q
  have hdelta : (i : ℝ) * delta ≤ q.eps ^ 2 / 4096 := by
    dsimp only [delta, figureOneExecutableMomentSlack]
    calc
      (i : ℝ) *
          (q.eps ^ 2 / (4096 * figureOneDependentPhaseCount q)) ≤
          figureOneDependentPhaseCount q *
            (q.eps ^ 2 / (4096 * figureOneDependentPhaseCount q)) :=
        mul_le_mul_of_nonneg_right hiR (by positivity)
      _ = q.eps ^ 2 / 4096 := by
        field_simp [hmR.ne']
  change (1 + delta) ^ i ≤ _
  exact hpow.trans (Real.exp_le_exp.mpr hdelta)

theorem figureOneExecutableMomentFactor_partialProduct_le_exp
    (q : VolumeParams) {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct (figureOneExecutableMomentFactor q) i ≤
      Real.exp (105 * q.eps ^ 2 / 4096) := by
  have hideal := figureOneChronologicalMomentFactor_partialProduct_le_exp q hi
  have hslack := figureOne_one_add_executableMomentSlack_pow_le_exp q hi
  have hideal0 : 0 ≤ dependentPhaseMeanProduct
      (figureOneChronologicalMomentFactor q) i :=
    dependentPhaseMeanProduct_nonneg _ (fun j =>
      zero_le_one.trans (figureOneChronologicalMomentFactor_one_le q j)) i
  have hslack0 : 0 ≤ (1 + figureOneExecutableMomentSlack q) ^ i :=
    pow_nonneg (by linarith [figureOneExecutableMomentSlack_nonneg q]) i
  rw [show dependentPhaseMeanProduct (figureOneExecutableMomentFactor q) i =
      dependentPhaseMeanProduct (figureOneChronologicalMomentFactor q) i *
        (1 + figureOneExecutableMomentSlack q) ^ i by
    unfold dependentPhaseMeanProduct figureOneExecutableMomentFactor
    rw [Finset.prod_mul_distrib]
    simp]
  calc
    _ ≤ Real.exp (13 * q.eps ^ 2 / 512) *
        Real.exp (q.eps ^ 2 / 4096) :=
      mul_le_mul hideal hslack hslack0 (Real.exp_pos _).le
    _ = Real.exp (105 * q.eps ^ 2 / 4096) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem figureOne_exp_113_eps_sq_div_4096_le (q : VolumeParams) :
    Real.exp (113 * q.eps ^ 2 / 4096) ≤ 1 + q.eps ^ 2 / 32 := by
  let y := q.eps ^ 2
  let x := 113 * y / 4096
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

/-- The explicit enlarged factors fit every finite prefix of the exact
budget consumed by the executable Lemma 7.15 capstone. -/
theorem figureOneExecutableMomentFactor_budget
    (q : VolumeParams) {i : ℕ} (hi : i ≤ figureOneDependentPhaseCount q) :
    dependentPhaseMeanProduct (figureOneExecutableMomentFactor q) i *
        ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2 ≤
      1 + q.eps ^ 2 / 32 := by
  have hfactor := figureOneExecutableMomentFactor_partialProduct_le_exp q hi
  have htrunc := figureOne_one_add_inv_alpha_pow_le_exp q hi
  have htrunc0 : 0 ≤ (1 + 1 / figureOneDependentAlpha q) ^ i := by
    apply pow_nonneg
    have ha := figureOneDependentAlpha_pos q
    have hinv : 0 ≤ 1 / figureOneDependentAlpha q :=
      (one_div_pos.mpr ha).le
    linarith
  have htruncSq : ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2 ≤
      Real.exp (q.eps ^ 2 / 1024) ^ 2 :=
    (sq_le_sq₀ htrunc0 (Real.exp_pos _).le).2 htrunc
  calc
    _ ≤ Real.exp (105 * q.eps ^ 2 / 4096) *
        Real.exp (q.eps ^ 2 / 1024) ^ 2 :=
      mul_le_mul hfactor htruncSq (sq_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (113 * q.eps ^ 2 / 4096) := by
      rw [show Real.exp (q.eps ^ 2 / 1024) ^ 2 =
        Real.exp (2 * (q.eps ^ 2 / 1024)) by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring,
        ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := figureOne_exp_113_eps_sq_div_4096_le q

/-- A coarse local second moment is enough to turn raw-product bias into the
truncated-product bias consumed by Lemma 7.15. -/
theorem scheduledFigureOneTrace_truncatedMeanProduct_relativeApprox_ideal_of_two
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q)) := by
  let ideal := ∏ phase, figureOneIdealPhaseMean q I phase
  let raw := dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
    (figureOneDependentPhaseCount q)
  let truncated := dependentPhaseMeanProduct
    (scheduledFigureOneTraceTruncatedMean q I)
      (figureOneDependentPhaseCount q)
  have hrawPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j :=
    fun j hj1 hjm => scheduledFigureOneTraceRawMean_pos q I j hj1 hjm
  have hidealPos : 0 < ideal := Finset.prod_pos fun phase _ =>
    figureOneIdealPhaseMean_pos q I phase
  have htruncated0 : 0 ≤ truncated :=
    dependentPhaseMeanProduct_nonneg _ (fun j =>
      scheduledFigureOneTraceTruncatedMean_nonnegative q I j <| by
        unfold scheduledFigureOneTraceRawMean
        exact integral_nonneg fun trace =>
          scheduledBalancedTracePhaseVariable_nonnegative q j trace) _
  have htruncatedRaw : truncated ≤ raw :=
    scheduledFigureOneTrace_truncatedMeanProduct_le_rawMeanProduct
      q I hrawPos (le_refl _)
  have hrawPow :=
    scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct_of_two
      q I hsecondTwo (le_refl _)
  have hpow := figureOne_one_add_inv_alpha_pow_le_exp q (le_refl _)
  have hrawExp : raw ≤ Real.exp (q.eps ^ 2 / 1024) * truncated :=
    hrawPow.trans (mul_le_mul_of_nonneg_right hpow htruncated0)
  have hrawBound : raw ≤ (1 + q.eps ^ 2 / 512) * truncated :=
    hrawExp.trans (mul_le_mul_of_nonneg_right
      (figureOne_exp_eps_sq_div_1024_le q) htruncated0)
  unfold RelativeApprox Arlib.relErr at hrawApprox ⊢
  change (1 - q.eps / 64) * ideal ≤ raw ∧
      raw ≤ (1 + q.eps / 64) * ideal at hrawApprox
  change (1 - q.eps / 32) * ideal ≤ truncated ∧
      truncated ≤ (1 + q.eps / 32) * ideal
  constructor
  · have hcoeff :
        (1 + q.eps ^ 2 / 512) * (1 - q.eps / 32) ≤
          1 - q.eps / 64 := by
      nlinarith [q.heps.1, q.heps.2,
        mul_nonneg q.heps.1.le (sub_nonneg.mpr q.heps.2.le)]
    have hscaled : (1 + q.eps ^ 2 / 512) *
        ((1 - q.eps / 32) * ideal) ≤
          (1 + q.eps ^ 2 / 512) * truncated := by
      calc
        _ = ((1 + q.eps ^ 2 / 512) * (1 - q.eps / 32)) * ideal := by ring
        _ ≤ (1 - q.eps / 64) * ideal :=
          mul_le_mul_of_nonneg_right hcoeff hidealPos.le
        _ ≤ raw := hrawApprox.1
        _ ≤ _ := hrawBound
    exact le_of_mul_le_mul_left hscaled (by positivity)
  · calc
      truncated ≤ raw := htruncatedRaw
      _ ≤ (1 + q.eps / 64) * ideal := hrawApprox.2
      _ ≤ (1 + q.eps / 32) * ideal := by
        apply mul_le_mul_of_nonneg_right _ hidealPos.le
        linarith [q.heps.1]

/-- Paper-faithful aborting accuracy with local truncation bias and global
second-product concentration separated.  This is the finite-walk slack form
of the remaining moment contract. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_slack_trace_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hproductSecond : ∀ i, i ≤ figureOneDependentPhaseCount q →
      dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        (1 + q.eps ^ 2 / 32) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I) i ^ 2)
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  apply figureOneFinalScheduledAbortBase_failure_le_of_directPostInitial q I oracle
  apply figureOnePostInitialDirectFailureBoundFor_of_trace_raw_moments
    q I oracle hrounded
  · intro j hj1 hjm
    exact memLp_scheduledBalancedForwardTrace_phaseVariable q I j hj1 hjm
  · intro j hj1 hjm
    exact scheduledFigureOneTraceRawMean_pos q I j hj1 hjm
  · intro j hj1 hjm
    exact (hsecondTwo j hj1 hjm).trans <| by
      gcongr
      norm_num
  · exact figureOneScheduledTrace_lemma717c q I
  · intro i hi
    let meanProduct := dependentPhaseMeanProduct
      (scheduledFigureOneTraceTruncatedMean q I) i
    have hmult := figureOneDependentMomentMultiplier_le q hi
    have hmult0 : 0 ≤ 1 + 2 * figureOneDependentEpsilon q *
        figureOneDependentAlpha q ^ 4 * (i : ℝ) := by
      have hterm : 0 ≤ 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * (i : ℝ) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num)
            (figureOneDependentEpsilon_nonneg q)) (by positivity))
          (by positivity)
      linarith
    calc
      _ ≤ (1 + 2 * figureOneDependentEpsilon q *
            figureOneDependentAlpha q ^ 4 * i) *
          ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
        mul_le_mul_of_nonneg_left (hproductSecond i hi) hmult0
      _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
          meanProduct ^ 2 := by
        have hscaled := mul_le_mul_of_nonneg_right hmult
          (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
        nlinarith
      _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
        mul_le_mul_of_nonneg_right (figureOneDependentMomentBudget_le q)
          (sq_nonneg meanProduct)
      _ ≤ 2 * meanProduct ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg meanProduct)
        nlinarith [q.heps.1, q.heps.2]
  · let meanProduct := dependentPhaseMeanProduct
      (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q)
    have hmult := figureOneDependentMomentMultiplier_le q (le_refl _)
    have hmult0 : 0 ≤ 1 + 2 * figureOneDependentEpsilon q *
        figureOneDependentAlpha q ^ 4 *
          (figureOneDependentPhaseCount q : ℝ) := by
      have hterm : 0 ≤ 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            (figureOneDependentPhaseCount q : ℝ) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num)
            (figureOneDependentEpsilon_nonneg q)) (by positivity))
          (by positivity)
      linarith
    calc
      _ ≤ (1 + 2 * figureOneDependentEpsilon q *
            figureOneDependentAlpha q ^ 4 *
              figureOneDependentPhaseCount q) *
          ((1 + q.eps ^ 2 / 32) * meanProduct ^ 2) :=
        mul_le_mul_of_nonneg_left
          (hproductSecond _ (le_refl _)) hmult0
      _ ≤ ((1 + q.eps ^ 2 / 2048) * (1 + q.eps ^ 2 / 32)) *
          meanProduct ^ 2 := by
        have hscaled := mul_le_mul_of_nonneg_right hmult
          (by positivity : 0 ≤ 1 + q.eps ^ 2 / 32)
        nlinarith
      _ ≤ (1 + q.eps ^ 2 / 16) * meanProduct ^ 2 :=
        mul_le_mul_of_nonneg_right (figureOneDependentMomentBudget_le q)
          (sq_nonneg meanProduct)
  · exact scheduledFigureOneTrace_truncatedMeanProduct_relativeApprox_ideal_of_two
      q I hsecondTwo hrawApprox

/-- Final executable accuracy in the precise factor language of CV18
Lemma 7.15, Eq. (6): the analytic collector proof supplies one phase factor,
and the paper's chunk calculation supplies its finite-prefix budget. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_phase_factor_budget
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (factor : ℕ → ℝ)
    (hfactor0 : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 ≤ factor j)
    (hfactorTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      factor j ≤ 2)
    (hsecondFactor : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        factor j * scheduledFigureOneTraceRawMean q I j ^ 2)
    (hbudget : ∀ i, i ≤ figureOneDependentPhaseCount q →
      dependentPhaseMeanProduct factor i *
          ((1 + 1 / figureOneDependentAlpha q) ^ i) ^ 2 ≤
        1 + q.eps ^ 2 / 32)
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  have hsecondTwo : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        2 * scheduledFigureOneTraceRawMean q I j ^ 2 := by
    intro j hj1 hjm
    exact (hsecondFactor j hj1 hjm).trans <|
      mul_le_mul_of_nonneg_right (hfactorTwo j hj1 hjm) (sq_nonneg _)
  apply figureOneFinalScheduledAbortBase_failure_le_of_slack_trace_moments
    q I oracle hrounded hsecondTwo
  · exact
      scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor_budget
        q I factor hfactor0 hsecondTwo hsecondFactor hbudget
  · exact hrawApprox

/-- The executable aborting theorem after all Lemma 7.15 product arithmetic
has been discharged.  Only the finite-walk empirical-average second moment
with the explicit per-phase slack, and the executable mean-product bias,
remain analytic inputs. -/
theorem figureOneFinalScheduledAbortBase_failure_le_of_executable_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hsecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneExecutableMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2)
    (hrawApprox : RelativeApprox (q.eps / 64)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct (scheduledFigureOneTraceRawMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledAbortBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  exact figureOneFinalScheduledAbortBase_failure_le_of_phase_factor_budget
    q I oracle hrounded (figureOneExecutableMomentFactor q)
    (fun j _ _ => figureOneExecutableMomentFactor_nonneg q j)
    (fun j _ _ => figureOneExecutableMomentFactor_le_two q j)
    hsecond (fun i hi => figureOneExecutableMomentFactor_budget q hi)
    hrawApprox

#print axioms
  scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean_of_two
#print axioms
  scheduledFigureOneTrace_rawMeanProduct_le_pow_mul_truncatedMeanProduct_of_two
#print axioms
  scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor
#print axioms
  scheduledFigureOneTrace_truncatedSecondProduct_le_of_factor_budget
#print axioms figureOne_one_add_executableMomentSlack_pow_le_exp
#print axioms figureOneExecutableMomentFactor_partialProduct_le_exp
#print axioms figureOne_exp_113_eps_sq_div_4096_le
#print axioms figureOneExecutableMomentFactor_budget
#print axioms figureOneExecutableMomentFactor_le_two
#print axioms
  scheduledFigureOneTrace_truncatedMeanProduct_relativeApprox_ideal_of_two
#print axioms
  figureOneFinalScheduledAbortBase_failure_le_of_slack_trace_moments
#print axioms
  figureOneFinalScheduledAbortBase_failure_le_of_phase_factor_budget
#print axioms
  figureOneFinalScheduledAbortBase_failure_le_of_executable_moments

end ArlibCommunity.Algorithms.CV18
