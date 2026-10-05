/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMomentBounds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-! # Product accuracy for ideal independent phase estimates

This file separates the standard probability calculation from the geometric
moment bounds and from the later coupling of the executable dependent walk to
ideal independent samples.
-/

/-- The standard exponential envelope for a product of nonnegative excess
second-moment factors. -/
theorem prod_one_add_le_exp_sum {ι : Type*} [Fintype ι]
    (delta : ι → ℝ) (hdelta : ∀ i, 0 ≤ delta i) :
    (∏ i, (1 + delta i)) ≤ Real.exp (∑ i, delta i) := by
  calc
    (∏ i, (1 + delta i)) ≤ ∏ i, Real.exp (delta i) := by
      apply Finset.prod_le_prod
      · intro i _
        linarith [hdelta i]
      · intro i _
        simpa [add_comm] using Real.add_one_le_exp (delta i)
    _ = Real.exp (∑ i, delta i) := by
      rw [← Real.exp_sum]

/-- If executable and ideal coordinates are coupled on one probability
space, any event for the executable tuple is bounded by the corresponding
ideal event plus the union of coordinate-mismatch events.  This is the exact
finite union-bound step used after the paper's sequential maximal coupling. -/
theorem measure_tuple_event_le_of_coordinate_coupling
    {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X Y : ι → Ω → α) (event : Set (ι → α)) :
    μ {ω | (fun i => X i ω) ∈ event} ≤
      μ {ω | (fun i => Y i ω) ∈ event} +
        ∑ i, μ {ω | X i ω ≠ Y i ω} := by
  have hsubset : {ω | (fun i => X i ω) ∈ event} ⊆
      {ω | (fun i => Y i ω) ∈ event} ∪
        ⋃ i, {ω | X i ω ≠ Y i ω} := by
    intro ω hω
    by_cases hall : ∀ i, X i ω = Y i ω
    · left
      have heq : (fun i => X i ω) = fun i => Y i ω := funext hall
      simpa [heq] using hω
    · right
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  calc
    μ {ω | (fun i => X i ω) ∈ event} ≤
        μ ({ω | (fun i => Y i ω) ∈ event} ∪
          ⋃ i, {ω | X i ω ≠ Y i ω}) := measure_mono hsubset
    _ ≤ μ {ω | (fun i => Y i ω) ∈ event} +
        μ (⋃ i, {ω | X i ω ≠ Y i ω}) := measure_union_le _ _
    _ ≤ μ {ω | (fun i => Y i ω) ∈ event} +
        ∑ i, μ {ω | X i ω ≠ Y i ω} := by
      gcongr
      exact measure_iUnion_fintype_le μ _

theorem measure_tuple_event_le_add_of_coordinate_coupling
    {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X Y : ι → Ω → α) (event : Set (ι → α))
    (error : ι → ℝ) (herror : ∀ i, μ {ω | X i ω ≠ Y i ω} ≤
      ENNReal.ofReal (error i)) :
    μ {ω | (fun i => X i ω) ∈ event} ≤
      μ {ω | (fun i => Y i ω) ∈ event} +
        ∑ i, ENNReal.ofReal (error i) := by
  refine (measure_tuple_event_le_of_coordinate_coupling μ X Y event).trans ?_
  gcongr with i
  exact herror i

theorem figureOneFixedSampleCount_cast_lower (q : VolumeParams) :
    4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2 ≤
      (figureOneFixedSampleCount q : ℝ) := by
  unfold figureOneFixedSampleCount
  exact Nat.le_ceil _

theorem figureOneSampleCount_cast_lower (q : VolumeParams) :
    512 * protectedLog (terminalVariance q) / q.eps ^ 2 ≤
      (figureOneSampleCount q : ℝ) := by
  unfold figureOneSampleCount
  exact Nat.le_ceil _

theorem figureOneSampleCount_pos (q : VolumeParams) :
    0 < figureOneSampleCount q := by
  have hH : 1 ≤ protectedLog (terminalVariance q) := le_max_left _ _
  have hlower := figureOneSampleCount_cast_lower q
  have hraw : (0 : ℝ) <
      512 * protectedLog (terminalVariance q) / q.eps ^ 2 := by
    exact div_pos
      (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hH))
      (sq_pos_of_pos q.heps.1)
  have : (0 : ℝ) < figureOneSampleCount q := hraw.trans_le hlower
  exact_mod_cast this

theorem figureOneFixedSampleCount_pos (q : VolumeParams) :
    0 < figureOneFixedSampleCount q := by
  have hL : 1 ≤ protectedLog ((q.n : ℝ) / q.eps) := le_max_left _ _
  have hlower := figureOneFixedSampleCount_cast_lower q
  have hraw : (0 : ℝ) <
      4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2 := by
    exact div_pos
      (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hL))
      (sq_pos_of_pos q.heps.1)
  have : (0 : ℝ) < figureOneFixedSampleCount q := hraw.trans_le hlower
  exact_mod_cast this

/-- The longer all-epsilon fixed-rate chain is exactly compensated by its
phase-sensitive sample count. -/
theorem fixedPhase_empiricalExcess_sum_le (q : VolumeParams) :
    ((slowPhaseSteps q : ℝ) * (2 / (q.n : ℝ))) /
        (figureOneFixedSampleCount q : ℝ) ≤ q.eps ^ 2 / 128 := by
  let n : ℝ := q.n
  let L : ℝ := protectedLog (n / q.eps)
  let k : ℝ := figureOneFixedSampleCount q
  have hn : 3 ≤ n := by
    dsimp [n]
    exact_mod_cast q.dim_ok
  have hn0 : 0 < n := by linarith
  have hL : 1 ≤ L := le_max_left _ _
  have he2 : 0 < q.eps ^ 2 := sq_pos_of_pos q.heps.1
  have hkLower : 4096 * L / q.eps ^ 2 ≤ k := by
    simpa [n, L, k] using figureOneFixedSampleCount_cast_lower q
  have hk : 0 < k := (by positivity : 0 < 4096 * L / q.eps ^ 2).trans_le hkLower
  have hsteps : (slowPhaseSteps q : ℝ) ≤ 15 * n * L := by
    simpa [n, L] using slowPhaseSteps_cast_le q
  rw [div_le_iff₀ hk]
  calc
    (slowPhaseSteps q : ℝ) * (2 / (q.n : ℝ)) ≤ 30 * L := by
      change (slowPhaseSteps q : ℝ) * (2 / n) ≤ 30 * L
      calc
        _ ≤ (15 * n * L) * (2 / n) := by gcongr
        _ = 30 * L := by
          field_simp [hn0.ne']
          norm_num
    _ ≤ 32 * L := by linarith
    _ = (q.eps ^ 2 / 128) * (4096 * L / q.eps ^ 2) := by
      field_simp [q.heps.1.ne']
      ring
    _ ≤ (q.eps ^ 2 / 128) * k := by gcongr

theorem fixedPhase_empiricalFactors_product_le
    (q : VolumeParams) {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι ≤ slowPhaseSteps q) :
    (∏ _i : ι, (1 +
        (2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ))) ≤
      Real.exp (q.eps ^ 2 / 128) := by
  let delta : ι → ℝ := fun _ =>
    (2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ)
  have hn0 : (0 : ℝ) < q.n := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) q.dim_ok)
  have hk0 : (0 : ℝ) < figureOneFixedSampleCount q := by
    have hL : 1 ≤ protectedLog ((q.n : ℝ) / q.eps) := le_max_left _ _
    have hlower := figureOneFixedSampleCount_cast_lower q
    have hraw : 0 <
        4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2 := by
      exact div_pos
        (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hL))
        (sq_pos_of_pos q.heps.1)
    exact hraw.trans_le hlower
  have hdelta : ∀ i, 0 ≤ delta i := fun _ => by
    dsimp [delta]
    positivity
  calc
    (∏ _i : ι, (1 +
        (2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ))) =
        ∏ i, (1 + delta i) := rfl
    _ ≤ Real.exp (∑ i, delta i) := prod_one_add_le_exp_sum delta hdelta
    _ ≤ Real.exp (q.eps ^ 2 / 128) := by
      apply Real.exp_le_exp.mpr
      have hcardR : (Fintype.card ι : ℝ) ≤ slowPhaseSteps q := by
        exact_mod_cast hcard
      calc
        (∑ i, delta i) =
            (Fintype.card ι : ℝ) *
              ((2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ)) := by
          simp [delta]
        _ ≤ (slowPhaseSteps q : ℝ) *
              ((2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ)) := by
          gcongr
        _ = ((slowPhaseSteps q : ℝ) * (2 / (q.n : ℝ))) /
              (figureOneFixedSampleCount q : ℝ) := by ring
        _ ≤ q.eps ^ 2 / 128 := fixedPhase_empiricalExcess_sum_le q

theorem scheduledFixedPhase_empiricalFactors_product_le (q : VolumeParams) :
    (∏ k ∈ Finset.range (terminalPhaseSteps q),
        if scheduleValue q k ≤ 1 then
          1 + (2 / (q.n : ℝ)) /
            (figureOneFixedSampleCount q : ℝ)
        else 1) ≤ Real.exp (q.eps ^ 2 / 128) := by
  classical
  let indices := (Finset.range (terminalPhaseSteps q)).filter
    fun k => scheduleValue q k ≤ 1
  have hsubset : indices ⊆ Finset.range (slowPhaseSteps q) := by
    intro k hk
    exact Finset.mem_range.mpr <|
      scheduleValue_le_one_imp_lt_slowPhaseSteps q (Finset.mem_filter.mp hk).2
  have hcard : Fintype.card indices ≤ slowPhaseSteps q := by
    simpa [indices] using Finset.card_le_card hsubset
  have hbound := fixedPhase_empiricalFactors_product_le q (hcard := hcard)
  calc
    (∏ k ∈ Finset.range (terminalPhaseSteps q),
        if scheduleValue q k ≤ 1 then
          1 + (2 / (q.n : ℝ)) /
            (figureOneFixedSampleCount q : ℝ)
        else 1) =
      ∏ k ∈ indices,
        (1 + (2 / (q.n : ℝ)) /
          (figureOneFixedSampleCount q : ℝ)) := by
        change (∏ k ∈ Finset.range (terminalPhaseSteps q),
            if scheduleValue q k ≤ 1 then _ else 1) =
          ∏ k ∈ (Finset.range (terminalPhaseSteps q)).filter
            (fun k => scheduleValue q k ≤ 1), _
        rw [Finset.prod_filter]
    _ = ∏ _k : indices,
        (1 + (2 / (q.n : ℝ)) /
          (figureOneFixedSampleCount q : ℝ)) := by
      simp
    _ ≤ Real.exp (q.eps ^ 2 / 128) := hbound

/-- Once the sharp CV18 accelerated factor is supplied, its empirical excess
has a small total charge across all accelerated transitions. -/
theorem acceleratedPhase_empiricalExcess_sum_le (q : VolumeParams) :
    (∑ k ∈ Finset.range (terminalPhaseSteps q),
        if 1 < scheduleValue q k then
          (scheduleValue q k / terminalVariance q) /
            (figureOneSampleCount q : ℝ)
        else 0) ≤ q.eps ^ 2 / 64 := by
  let T : ℝ := terminalVariance q
  let H : ℝ := protectedLog T
  let samples : ℝ := figureOneSampleCount q
  have hT : 0 < T := by
    dsimp [T]
    exact terminalVariance_pos' q
  have hH : 1 ≤ H := le_max_left _ _
  have he2 : 0 < q.eps ^ 2 := sq_pos_of_pos q.heps.1
  have hsamplesLower : 512 * H / q.eps ^ 2 ≤ samples := by
    simpa [T, H, samples] using figureOneSampleCount_cast_lower q
  have hsamples : 0 < samples := by
    have hraw : 0 < 512 * H / q.eps ^ 2 := by positivity
    exact hraw.trans_le hsamplesLower
  have hsum := sum_accelerated_scheduleValue_le q
  have hsum' :
      (∑ k ∈ Finset.range (terminalPhaseSteps q),
          if 1 < scheduleValue q k then scheduleValue q k else 0) ≤
        5 * T * H := by
    change _ ≤ 4 * T * H + T at hsum
    calc
      _ ≤ 4 * T * H + T := hsum
      _ ≤ 5 * T * H := by
        nlinarith [mul_nonneg hT.le (sub_nonneg.mpr hH)]
  have hrewrite :
      (∑ k ∈ Finset.range (terminalPhaseSteps q),
      if 1 < scheduleValue q k then
        (scheduleValue q k / T) / samples else 0) =
        (1 / T / samples) *
          (∑ k ∈ Finset.range (terminalPhaseSteps q),
            if 1 < scheduleValue q k then scheduleValue q k else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> ring
  change (∑ k ∈ Finset.range (terminalPhaseSteps q),
      if 1 < scheduleValue q k then
        (scheduleValue q k / T) / samples else 0) ≤ _
  rw [hrewrite]
  calc
    (1 / T / samples) *
        (∑ k ∈ Finset.range (terminalPhaseSteps q),
          if 1 < scheduleValue q k then scheduleValue q k else 0) ≤
      (1 / T / samples) * (5 * T * H) := by gcongr
    _ = 5 * H / samples := by field_simp [hT.ne', hsamples.ne']
    _ ≤ 5 * H / (512 * H / q.eps ^ 2) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsamplesLower
    _ = 5 * q.eps ^ 2 / 512 := by
      field_simp [show H ≠ 0 by linarith, q.heps.1.ne']
    _ ≤ q.eps ^ 2 / 64 := by nlinarith

theorem acceleratedPhase_empiricalFactors_product_le (q : VolumeParams) :
    (∏ k ∈ Finset.range (terminalPhaseSteps q),
        if 1 < scheduleValue q k then
          1 + (scheduleValue q k / terminalVariance q) /
            (figureOneSampleCount q : ℝ)
        else 1) ≤ Real.exp (q.eps ^ 2 / 64) := by
  let delta : ℕ → ℝ := fun k =>
    if 1 < scheduleValue q k then
      (scheduleValue q k / terminalVariance q) /
        (figureOneSampleCount q : ℝ)
    else 0
  have hsamples : (0 : ℝ) < figureOneSampleCount q := by
    have hH : 1 ≤ protectedLog (terminalVariance q) := le_max_left _ _
    have hlower := figureOneSampleCount_cast_lower q
    have hraw : 0 <
        512 * protectedLog (terminalVariance q) / q.eps ^ 2 := by
      exact div_pos
        (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hH))
        (sq_pos_of_pos q.heps.1)
    exact hraw.trans_le hlower
  have hdelta : ∀ k, 0 ≤ delta k := by
    intro k
    dsimp [delta]
    split_ifs
    · exact div_nonneg
        (div_nonneg (scheduleValue_pos q k).le
          (terminalVariance_pos' q).le)
        hsamples.le
    · exact le_rfl
  calc
    (∏ k ∈ Finset.range (terminalPhaseSteps q),
        if 1 < scheduleValue q k then
          1 + (scheduleValue q k / terminalVariance q) /
            (figureOneSampleCount q : ℝ)
        else 1) =
      ∏ k ∈ Finset.range (terminalPhaseSteps q), (1 + delta k) := by
        apply Finset.prod_congr rfl
        intro k hk
        dsimp [delta]
        split_ifs <;> ring
    _ ≤ Real.exp (∑ k ∈ Finset.range (terminalPhaseSteps q), delta k) := by
      rw [← Finset.prod_coe_sort, ← Finset.sum_coe_sort]
      exact prod_one_add_le_exp_sum
        (fun k : Finset.range (terminalPhaseSteps q) => delta k)
        (fun k => hdelta k)
    _ ≤ Real.exp (q.eps ^ 2 / 64) := by
      apply Real.exp_le_exp.mpr
      simpa [delta] using acceleratedPhase_empiricalExcess_sum_le q

theorem exp_half_sub_one_le_one : Real.exp (1 / 2) - 1 ≤ (1 : ℝ) := by
  have h := Real.exp_le_two_add_div_two_sub
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 < 2 by norm_num)
  norm_num at h ⊢
  linarith

theorem terminalPhase_empiricalExcess_le (q : VolumeParams) :
    (Real.exp (1 / 2) - 1) / (figureOneSampleCount q : ℝ) ≤
      q.eps ^ 2 / 512 := by
  let H : ℝ := protectedLog (terminalVariance q)
  let samples : ℝ := figureOneSampleCount q
  have hH : 1 ≤ H := le_max_left _ _
  have hsamplesLower : 512 * H / q.eps ^ 2 ≤ samples := by
    simpa [H, samples] using figureOneSampleCount_cast_lower q
  have hraw : 0 < 512 * H / q.eps ^ 2 := by
    exact div_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hH))
      (sq_pos_of_pos q.heps.1)
  have hsamples : 0 < samples := by
    exact hraw.trans_le hsamplesLower
  have hnum0 : 0 ≤ Real.exp (1 / 2) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  calc
    (Real.exp (1 / 2) - 1) / samples ≤ 1 / samples := by
      exact div_le_div_of_nonneg_right exp_half_sub_one_le_one hsamples.le
    _ ≤ 1 / (512 * H / q.eps ^ 2) := by
      exact one_div_le_one_div_of_le hraw hsamplesLower
    _ ≤ 1 / (512 / q.eps ^ 2) := by
      apply one_div_le_one_div_of_le
        (div_pos (by norm_num) (sq_pos_of_pos q.heps.1))
      have he2 : 0 < q.eps ^ 2 := sq_pos_of_pos q.heps.1
      rw [div_le_div_iff₀ he2 he2]
      nlinarith
    _ = q.eps ^ 2 / 512 := by
      field_simp [q.heps.1.ne']

/-- The complete ideal empirical product (all Gaussian phases plus the final
Gaussian-to-uniform phase) has the small relative second-moment factor needed
by the Chebyshev step, conditional only on the sharp accelerated per-phase
factor `1 + sigma² / terminalVariance`. -/
theorem idealEmpiricalProduct_factor_le (q : VolumeParams) :
    ((∏ k ∈ Finset.range (terminalPhaseSteps q),
        if scheduleValue q k ≤ 1 then
          1 + (2 / (q.n : ℝ)) /
            (figureOneFixedSampleCount q : ℝ)
        else
          1 + (scheduleValue q k / terminalVariance q) /
            (figureOneSampleCount q : ℝ)) *
      (1 + (Real.exp (1 / 2) - 1) /
        (figureOneSampleCount q : ℝ))) ≤
      Real.exp (13 * q.eps ^ 2 / 512) := by
  let fixed : ℕ → ℝ := fun k =>
    if scheduleValue q k ≤ 1 then
      1 + (2 / (q.n : ℝ)) / (figureOneFixedSampleCount q : ℝ)
    else 1
  let accelerated : ℕ → ℝ := fun k =>
    if 1 < scheduleValue q k then
      1 + (scheduleValue q k / terminalVariance q) /
        (figureOneSampleCount q : ℝ)
    else 1
  have hsplit :
      (∏ k ∈ Finset.range (terminalPhaseSteps q),
        if scheduleValue q k ≤ 1 then
          1 + (2 / (q.n : ℝ)) /
            (figureOneFixedSampleCount q : ℝ)
        else
          1 + (scheduleValue q k / terminalVariance q) /
            (figureOneSampleCount q : ℝ)) =
      (∏ k ∈ Finset.range (terminalPhaseSteps q), fixed k) *
        (∏ k ∈ Finset.range (terminalPhaseSteps q), accelerated k) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    dsimp [fixed, accelerated]
    by_cases hs : scheduleValue q k ≤ 1
    · simp [hs, not_lt_of_ge hs]
    · simp [hs, lt_of_not_ge hs]
  have hfixed :
      (∏ k ∈ Finset.range (terminalPhaseSteps q), fixed k) ≤
        Real.exp (q.eps ^ 2 / 128) := by
    simpa [fixed] using scheduledFixedPhase_empiricalFactors_product_le q
  have haccelerated :
      (∏ k ∈ Finset.range (terminalPhaseSteps q), accelerated k) ≤
        Real.exp (q.eps ^ 2 / 64) := by
    simpa [accelerated] using acceleratedPhase_empiricalFactors_product_le q
  have hphase :
      (∏ k ∈ Finset.range (terminalPhaseSteps q),
        if scheduleValue q k ≤ 1 then
          1 + (2 / (q.n : ℝ)) /
            (figureOneFixedSampleCount q : ℝ)
        else
          1 + (scheduleValue q k / terminalVariance q) /
            (figureOneSampleCount q : ℝ)) ≤
        Real.exp (3 * q.eps ^ 2 / 128) := by
    rw [hsplit]
    have haccelerated0 : 0 ≤
        ∏ k ∈ Finset.range (terminalPhaseSteps q), accelerated k := by
      apply Finset.prod_nonneg
      intro k hk
      dsimp [accelerated]
      split_ifs
      · have hsamples : (0 : ℝ) < figureOneSampleCount q := by
          exact_mod_cast figureOneSampleCount_pos q
        have hratio : 0 ≤
            (scheduleValue q k / terminalVariance q) /
              (figureOneSampleCount q : ℝ) :=
          div_nonneg
            (div_nonneg (scheduleValue_pos q k).le
              (terminalVariance_pos' q).le) hsamples.le
        linarith
      · norm_num
    calc
      _ ≤ Real.exp (q.eps ^ 2 / 128) *
          (∏ k ∈ Finset.range (terminalPhaseSteps q), accelerated k) :=
        mul_le_mul_of_nonneg_right hfixed haccelerated0
      _ ≤ Real.exp (q.eps ^ 2 / 128) * Real.exp (q.eps ^ 2 / 64) :=
        mul_le_mul_of_nonneg_left haccelerated (Real.exp_pos _).le
      _ = Real.exp (3 * q.eps ^ 2 / 128) := by
        rw [← Real.exp_add]
        congr 1
        ring
  let terminalDelta := (Real.exp (1 / 2) - 1) /
    (figureOneSampleCount q : ℝ)
  have hterminalDelta0 : 0 ≤ terminalDelta := by
    dsimp [terminalDelta]
    have hsamples : (0 : ℝ) < figureOneSampleCount q := by
      exact_mod_cast figureOneSampleCount_pos q
    exact div_nonneg
      (sub_nonneg.mpr (Real.one_le_exp (by norm_num))) hsamples.le
  have hterminal : 1 + terminalDelta ≤ Real.exp (q.eps ^ 2 / 512) := by
    calc
      1 + terminalDelta ≤ Real.exp terminalDelta := by
        simpa [add_comm] using Real.add_one_le_exp terminalDelta
      _ ≤ Real.exp (q.eps ^ 2 / 512) := by
        apply Real.exp_le_exp.mpr
        simpa [terminalDelta] using terminalPhase_empiricalExcess_le q
  change _ * (1 + terminalDelta) ≤ _
  calc
    _ ≤ Real.exp (3 * q.eps ^ 2 / 128) * (1 + terminalDelta) :=
      mul_le_mul_of_nonneg_right hphase (by linarith)
    _ ≤ Real.exp (3 * q.eps ^ 2 / 128) *
        Real.exp (q.eps ^ 2 / 512) :=
      mul_le_mul_of_nonneg_left hterminal (Real.exp_pos _).le
    _ = Real.exp (13 * q.eps ^ 2 / 512) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem idealEmpiricalProduct_exponentialExcess_le (q : VolumeParams) :
    Real.exp (13 * q.eps ^ 2 / 512) - 1 ≤ q.eps ^ 2 / 32 := by
  let y := q.eps ^ 2
  let x := 13 * y / 512
  have hy0 : 0 ≤ y := sq_nonneg q.eps
  have hy1 : y ≤ 1 := by
    dsimp [y]
    nlinarith [q.heps.1, q.heps.2]
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x < 2 := by
    dsimp [x]
    nlinarith
  have hexp : Real.exp x ≤ (2 + x) / (2 - x) :=
    Real.exp_le_two_add_div_two_sub hx0 hx2
  have hrational : (2 + x) / (2 - x) ≤ 1 + y / 32 := by
    rw [div_le_iff₀ (sub_pos.mpr hx2)]
    dsimp [x]
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  change Real.exp x - 1 ≤ y / 32
  linarith

/-- Chebyshev in the relative-error form used by the cooling product. -/
theorem measure_relativeDeviation_le_of_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {target eps delta : ℝ} (htarget : 0 < target) (heps : 0 < eps)
    (hmean : ∫ ω, X ω ∂μ = target)
    (hsecond : (∫ ω, X ω ^ 2 ∂μ) ≤ (1 + delta) * target ^ 2) :
    μ {ω | eps * target ≤ |X ω - target|} ≤
      ENNReal.ofReal (delta / eps ^ 2) := by
  have hvariance : variance X μ ≤ delta * target ^ 2 := by
    rw [variance_eq_sub hX, hmean]
    change (∫ ω, X ω ^ 2 ∂μ) - target ^ 2 ≤ delta * target ^ 2
    nlinarith [sq_nonneg target]
  have hcheb := meas_ge_le_variance_div_sq hX (mul_pos heps htarget)
  rw [hmean] at hcheb
  refine hcheb.trans ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    variance X μ / (eps * target) ^ 2 ≤
        (delta * target ^ 2) / (eps * target) ^ 2 := by
      exact div_le_div_of_nonneg_right hvariance (sq_nonneg _)
    _ = delta / eps ^ 2 := by
      field_simp [heps.ne', htarget.ne']

/-- Independence factors both the first and second moments of a finite
product. -/
theorem iIndepFun_product_moments
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) {X : ι → Ω → ℝ}
    (hind : iIndepFun X μ)
    (hmeas : ∀ i, AEStronglyMeasurable (X i) μ) :
    (∫ ω, ∏ i, X i ω ∂μ) = ∏ i, ∫ ω, X i ω ∂μ ∧
      (∫ ω, (∏ i, X i ω) ^ 2 ∂μ) = ∏ i, ∫ ω, X i ω ^ 2 ∂μ := by
  constructor
  · exact hind.integral_fun_prod_eq_prod_integral hmeas
  · let Y : ι → Ω → ℝ := fun i ω => X i ω ^ 2
    have hYind : iIndepFun Y μ := by
      let sq : ∀ _ : ι, ℝ → ℝ := fun _ x => x ^ 2
      have hcomp := hind.comp sq (by
        intro i
        dsimp [sq]
        fun_prop)
      simpa [Y, Function.comp_def] using hcomp
    have hYmeas : ∀ i, AEStronglyMeasurable (Y i) μ :=
      fun i => (hmeas i).pow 2
    have hprod := hYind.integral_fun_prod_eq_prod_integral hYmeas
    simpa only [Y, ← Finset.prod_pow] using hprod

/-- Averaging `k` independent copies divides the excess relative second
moment by `k`, which is equation (19) in the paper's accuracy calculation. -/
theorem independent_empiricalMean_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k)
    {Y : Fin k → Ω → ℝ} (hind : iIndepFun Y μ)
    (hY : ∀ i, MemLp (Y i) 2 μ) {mean factor : ℝ}
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = mean)
    (hsecond : ∀ i, (∫ ω, Y i ω ^ 2 ∂μ) ≤ factor * mean ^ 2) :
    let average : Ω → ℝ := fun ω => (∑ i, Y i ω) / (k : ℝ)
    (∫ ω, average ω ∂μ) = mean ∧
      (∫ ω, average ω ^ 2 ∂μ) ≤
        (1 + (factor - 1) / (k : ℝ)) * mean ^ 2 := by
  let average : Ω → ℝ := fun ω => (∑ i, Y i ω) / (k : ℝ)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsumLp : MemLp (fun ω => ∑ i, Y i ω) 2 μ :=
    memLp_finsetSum Finset.univ fun i _ => hY i
  have havgLp : MemLp average 2 μ := by
    have h := hsumLp.const_mul (1 / (k : ℝ))
    simpa [average, div_eq_mul_inv, mul_comm] using h
  have havgMean : ∫ ω, average ω ∂μ = mean := by
    dsimp [average]
    rw [integral_div, integral_finsetSum Finset.univ
      (fun i _ => (hY i).integrable one_le_two)]
    simp_rw [hmean]
    simp [hk.ne']
  refine ⟨havgMean, ?_⟩
  have hpair : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise
      fun i j => Y i ⟂ᵢ[μ] Y j := by
    intro i _ j _ hij
    exact hind.indepFun hij
  have hvarsum := IndepFun.variance_sum
    (s := (Finset.univ : Finset (Fin k))) (fun i _ => hY i) hpair
  have hvarEach : ∀ i, variance (Y i) μ ≤ (factor - 1) * mean ^ 2 := by
    intro i
    rw [variance_eq_sub (hY i), hmean i]
    change (∫ ω, Y i ω ^ 2 ∂μ) - mean ^ 2 ≤ (factor - 1) * mean ^ 2
    nlinarith [hsecond i]
  have hvarsum_le : variance (fun ω => ∑ i, Y i ω) μ ≤
      (k : ℝ) * ((factor - 1) * mean ^ 2) := by
    rw [show (fun ω => ∑ i, Y i ω) = ∑ i, Y i by
      funext ω
      symm
      simp]
    rw [hvarsum]
    calc
      ∑ i : Fin k, variance (Y i) μ ≤
          ∑ _i : Fin k, (factor - 1) * mean ^ 2 := by
        exact Finset.sum_le_sum fun i _ => hvarEach i
      _ = (k : ℝ) * ((factor - 1) * mean ^ 2) := by simp
  have hvaravg : variance average μ ≤
      ((factor - 1) / (k : ℝ)) * mean ^ 2 := by
    rw [show average = fun ω => (1 / (k : ℝ)) * (∑ i, Y i ω) by
      funext ω
      simp [average, div_eq_mul_inv, mul_comm]]
    rw [variance_const_mul]
    calc
      (1 / (k : ℝ)) ^ 2 * variance (fun ω => ∑ i, Y i ω) μ ≤
          (1 / (k : ℝ)) ^ 2 *
            ((k : ℝ) * ((factor - 1) * mean ^ 2)) := by
        gcongr
      _ = ((factor - 1) / (k : ℝ)) * mean ^ 2 := by
        field_simp [hkR.ne']
  rw [variance_eq_sub havgLp, havgMean] at hvaravg
  change (∫ ω, average ω ^ 2 ∂μ) ≤
      (1 + (factor - 1) / (k : ℝ)) * mean ^ 2
  change (∫ ω, average ω ^ 2 ∂μ) - mean ^ 2 ≤
      ((factor - 1) / (k : ℝ)) * mean ^ 2 at hvaravg
  nlinarith

/-- Canonical realization of an independent empirical mean on the finite
product probability space.  This turns the abstract independence lemma above
into the exact ideal sampler used for each cooling phase. -/
theorem independent_empiricalMean_moments_pi
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    {k : ℕ} (hk : 0 < k) {w : α → ℝ} (hw : MemLp w 2 ν)
    {mean factor : ℝ}
    (hmean : ∫ x, w x ∂ν = mean)
    (hsecond : (∫ x, w x ^ 2 ∂ν) ≤ factor * mean ^ 2) :
    let μ : Measure (Fin k → α) := Measure.pi fun _ => ν
    let average : (Fin k → α) → ℝ :=
      fun ω => (∑ i, w (ω i)) / (k : ℝ)
    (∫ ω, average ω ∂μ) = mean ∧
      (∫ ω, average ω ^ 2 ∂μ) ≤
        (1 + (factor - 1) / (k : ℝ)) * mean ^ 2 := by
  let μ : Measure (Fin k → α) := Measure.pi fun _ => ν
  let Y : Fin k → (Fin k → α) → ℝ := fun i ω => w (ω i)
  let average : (Fin k → α) → ℝ :=
    fun ω => (∑ i, w (ω i)) / (k : ℝ)
  have hind : iIndepFun Y μ := by
    exact iIndepFun_pi fun _ => hw.aestronglyMeasurable.aemeasurable
  have hY : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    exact hw.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin k => ν) i)
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = mean := by
    intro i
    rw [show Y i = fun ω => w (ω i) by rfl,
      integral_comp_eval hw.aestronglyMeasurable, hmean]
  have hYsecond : ∀ i, (∫ ω, Y i ω ^ 2 ∂μ) ≤
      factor * mean ^ 2 := by
    intro i
    have hsq : AEStronglyMeasurable (fun x => w x ^ 2) ν :=
      hw.aestronglyMeasurable.pow 2
    change (∫ ω, (fun x => w x ^ 2) (ω i)
      ∂Measure.pi (fun _ : Fin k => ν)) ≤ _
    rw [integral_comp_eval (μ := fun _ : Fin k => ν) (i := i) hsq]
    exact hsecond
  simpa [μ, Y, average] using
    independent_empiricalMean_moments μ hk hind hY hYmean hYsecond

/-- The empirical-average coordinate map on the canonical finite product
space. -/
noncomputable def idealEmpiricalAverage {α : Type*} [MeasurableSpace α]
    (k : ℕ) (w : α → ℝ) (samples : Fin k → α) : ℝ :=
  (∑ i, w (samples i)) / (k : ℝ)

theorem measurable_idealEmpiricalAverage
    {α : Type*} [MeasurableSpace α] (k : ℕ) {w : α → ℝ}
    (hw : Measurable w) :
    Measurable (idealEmpiricalAverage k w) := by
  unfold idealEmpiricalAverage
  exact (Finset.univ.measurable_fun_sum fun i _ =>
    hw.comp (measurable_pi_apply i)).div_const _

/-- A stationary relative-second-moment estimate gives the corresponding
first and second moments of the canonical independent empirical average. -/
theorem idealEmpiricalAverage_moments_of_relativeSecondMoment
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    {k : ℕ} (hk : 0 < k) {w : α → ℝ} (hw : MemLp w 2 ν)
    {mean factor : ℝ} (hmeanpos : 0 < mean)
    (hmean : ∫ x, w x ∂ν = mean)
    (hrelative : (∫ x, w x ^ 2 ∂ν) / mean ^ 2 ≤ factor) :
    let μ : Measure (Fin k → α) := Measure.pi fun _ => ν
    (∫ samples, idealEmpiricalAverage k w samples ∂μ) = mean ∧
      (∫ samples, (idealEmpiricalAverage k w samples) ^ 2 ∂μ) ≤
        (1 + (factor - 1) / (k : ℝ)) * mean ^ 2 := by
  have hsecond : (∫ x, w x ^ 2 ∂ν) ≤ factor * mean ^ 2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hmeanpos)).mp hrelative
  simpa [idealEmpiricalAverage] using
    independent_empiricalMean_moments_pi ν hk hw hmean hsecond

/-- The canonical ideal empirical average at a fixed-rate scheduled phase has
the exact ratio mean and the checked `1 + (2/n)/k` second-moment factor. -/
theorem scheduledFixedIdealEmpiricalAverage_moments
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hsone : scheduleValue q k ≤ 1) :
    let ν : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k)
    let count := figureOneFixedSampleCount q
    let weight := gaussianRatioWeight (n := q.n)
      (scheduleValue q k) (scheduleValue q (k + 1))
    let mean := gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
      gaussianIntegral (truncatedBody q I) (scheduleValue q k)
    (∫ samples, idealEmpiricalAverage count weight samples
        ∂Measure.pi (fun _ : Fin count => ν)) = mean ∧
      (∫ samples, (idealEmpiricalAverage count weight samples) ^ 2
        ∂Measure.pi (fun _ : Fin count => ν)) ≤
          (1 + (2 / (q.n : ℝ)) / (count : ℝ)) * mean ^ 2 := by
  let ν : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q k)
      (scheduleValue_pos q k)
  let count := figureOneFixedSampleCount q
  let weight := gaussianRatioWeight (n := q.n)
    (scheduleValue q k) (scheduleValue q (k + 1))
  let mean := gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
    gaussianIntegral (truncatedBody q I) (scheduleValue q k)
  have ht : 0 < scheduleValue q (k + 1) := scheduleValue_pos q (k + 1)
  have hmeanpos : 0 < mean := by
    dsimp [mean]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I) ht)
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q k))
  have hmean : ∫ x, weight x ∂ν = mean := by
    simpa [ν, weight, mean] using gaussianRatioWeight_mean_eq
      q I (scheduleValue_pos q k)
  have hrel := scheduleValue_fixedRate_relativeSecondMoment_le q I k hsone
  have hrel' : (∫ x, weight x ^ 2 ∂ν) / mean ^ 2 ≤
      1 + 2 / (q.n : ℝ) := by
    rw [← hmean]
    simpa [ν, weight] using hrel
  have hbase := idealEmpiricalAverage_moments_of_relativeSecondMoment
    ν (show 0 < count by
      simpa [count] using figureOneFixedSampleCount_pos q)
    (gaussianRatioWeight_memLp q I (scheduleValue_pos q k) ht 2)
    hmeanpos hmean hrel'
  simpa [ν, count, weight, mean] using hbase

/-- Once the sharp accelerated stationary bound is supplied, the canonical
ideal empirical phase has exactly the factor used by the logarithmic
accumulation theorem above. -/
theorem scheduledAcceleratedIdealEmpiricalAverage_moments_of_relativeSecondMoment
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (_hsone : 1 < scheduleValue q k)
    (hrelative :
      (∫ x, gaussianRatioWeight (scheduleValue q k)
            (scheduleValue q (k + 1)) x ^ 2
          ∂(truncatedGaussianProbability q I (scheduleValue q k)
            (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
        (∫ x, gaussianRatioWeight (scheduleValue q k)
            (scheduleValue q (k + 1)) x
          ∂(truncatedGaussianProbability q I (scheduleValue q k)
            (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 2 ≤
        1 + scheduleValue q k / terminalVariance q) :
    let ν : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k)
    let count := figureOneSampleCount q
    let weight := gaussianRatioWeight (n := q.n)
      (scheduleValue q k) (scheduleValue q (k + 1))
    let mean := gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
      gaussianIntegral (truncatedBody q I) (scheduleValue q k)
    (∫ samples, idealEmpiricalAverage count weight samples
        ∂Measure.pi (fun _ : Fin count => ν)) = mean ∧
      (∫ samples, (idealEmpiricalAverage count weight samples) ^ 2
        ∂Measure.pi (fun _ : Fin count => ν)) ≤
          (1 + (scheduleValue q k / terminalVariance q) /
            (count : ℝ)) * mean ^ 2 := by
  let ν : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (scheduleValue q k)
      (scheduleValue_pos q k)
  let count := figureOneSampleCount q
  let weight := gaussianRatioWeight (n := q.n)
    (scheduleValue q k) (scheduleValue q (k + 1))
  let mean := gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
    gaussianIntegral (truncatedBody q I) (scheduleValue q k)
  have ht : 0 < scheduleValue q (k + 1) := scheduleValue_pos q (k + 1)
  have hmeanpos : 0 < mean := by
    dsimp [mean]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I) ht)
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q k))
  have hmean : ∫ x, weight x ∂ν = mean := by
    simpa [ν, weight, mean] using gaussianRatioWeight_mean_eq
      q I (scheduleValue_pos q k)
  have hrel' : (∫ x, weight x ^ 2 ∂ν) / mean ^ 2 ≤
      1 + scheduleValue q k / terminalVariance q := by
    rw [← hmean]
    simpa [ν, weight] using hrelative
  have hbase := idealEmpiricalAverage_moments_of_relativeSecondMoment
    ν (show 0 < count by simpa [count] using figureOneSampleCount_pos q)
    (gaussianRatioWeight_memLp q I (scheduleValue_pos q k) ht 2)
    hmeanpos hmean hrel'
  simpa [ν, count, weight, mean] using hbase

/-- The canonical ideal terminal empirical average has the exact
Gaussian-to-uniform ratio mean and the terminal factor used in the complete
product calculation. -/
theorem terminalIdealEmpiricalAverage_moments
    (q : VolumeParams) (I : VolumeInput q.n) :
    let ν : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q)
    let count := figureOneSampleCount q
    let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
    let mean := euclideanVolume (truncatedVolumeInput q I) /
      gaussianIntegral (truncatedBody q I) (terminalVariance q)
    (∫ samples, idealEmpiricalAverage count weight samples
        ∂Measure.pi (fun _ : Fin count => ν)) = mean ∧
      (∫ samples, (idealEmpiricalAverage count weight samples) ^ 2
        ∂Measure.pi (fun _ : Fin count => ν)) ≤
          (1 + (Real.exp (1 / 2) - 1) / (count : ℝ)) * mean ^ 2 := by
  let ν : Measure (AmbientSpace q.n) :=
    truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q)
  let count := figureOneSampleCount q
  let weight := uniformRatioWeight (n := q.n) (terminalVariance q)
  let mean := euclideanVolume (truncatedVolumeInput q I) /
    gaussianIntegral (truncatedBody q I) (terminalVariance q)
  have hmeanpos : 0 < mean := by
    dsimp [mean]
    exact div_pos
      (euclideanVolume_pos q (truncatedVolumeInput q I))
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (terminalVariance_pos' q))
  have hmean : ∫ x, weight x ∂ν = mean := by
    simpa [ν, weight, mean] using uniformRatioWeight_mean_eq
      q I (terminalVariance_pos' q)
  have hrelative := uniformRatioWeight_terminal_relativeSecondMoment_le q I
  have hrel' : (∫ x, weight x ^ 2 ∂ν) / mean ^ 2 ≤ Real.exp (1 / 2) := by
    rw [← hmean]
    simpa [ν, weight] using hrelative
  have hbase := idealEmpiricalAverage_moments_of_relativeSecondMoment
    ν (show 0 < count by simpa [count] using figureOneSampleCount_pos q)
    (uniformRatioWeight_memLp q I (terminalVariance_pos' q) 2)
    hmeanpos hmean hrel'
  simpa [ν, count, weight, mean] using hbase

/-- Independent positive phase estimators inherit a relative-error tail bound
from the product of their relative second-moment factors. -/
theorem measure_independent_product_relativeDeviation_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hind : iIndepFun X μ) (hmeas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hprodLp : MemLp (fun ω => ∏ i, X i ω) 2 μ)
    {mean factor : ι → ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂μ = mean i)
    (hmeanpos : ∀ i, 0 < mean i) (hfactor : ∀ i, 1 ≤ factor i)
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) ≤ factor i * mean i ^ 2)
    {eps : ℝ} (heps : 0 < eps) :
    μ {ω | eps * (∏ i, mean i) ≤ |(∏ i, X i ω) - ∏ i, mean i|} ≤
      ENNReal.ofReal ((∏ i, factor i) - 1) / ENNReal.ofReal (eps ^ 2) := by
  have hmoments := iIndepFun_product_moments μ hind hmeas
  have htarget : 0 < ∏ i, mean i := Finset.prod_pos fun i _ => hmeanpos i
  have hfactorprod : 1 ≤ ∏ i, factor i := by
    exact Finset.one_le_prod fun i _ => hfactor i
  have hsecondprod : (∫ ω, (∏ i, X i ω) ^ 2 ∂μ) ≤
      (∏ i, factor i) * (∏ i, mean i) ^ 2 := by
    rw [hmoments.2]
    calc
      (∏ i, ∫ ω, X i ω ^ 2 ∂μ) ≤ ∏ i, factor i * mean i ^ 2 := by
        apply Finset.prod_le_prod
        · intro i _
          exact integral_nonneg fun _ => sq_nonneg _
        · intro i _
          exact hsecond i
      _ = (∏ i, factor i) * (∏ i, mean i) ^ 2 := by
        rw [Finset.prod_mul_distrib, ← Finset.prod_pow]
  have h := measure_relativeDeviation_le_of_secondMoment
    (delta := (∏ i, factor i) - 1) μ hprodLp htarget heps
    (by simp [hmoments.1, hmean]) (by
      convert hsecondprod using 1
      ring)
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos heps)] at h
  exact h

end ArlibCommunity.Algorithms.CV18
