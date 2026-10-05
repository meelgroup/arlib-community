/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPrimitives
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSchedule

namespace ArlibCommunity.Algorithms.CV18

open scoped BigOperators

private theorem figureOneCoolingQueryBudget_ofFn
    (q : VolumeParams) : ∀ (N : ℕ) (f : Fin (N + 1) → ℝ),
    figureOneCoolingQueryBudget q (List.ofFn f) =
      ∑ k : Fin N, figureOnePhaseSampleCount q (f k.castSucc) *
        figureOneWalkSteps q (f k.castSucc) := by
  intro N
  induction N with
  | zero =>
      intro f
      simp [List.ofFn_succ, figureOneCoolingQueryBudget]
  | succ N ih =>
      intro f
      rw [List.ofFn_succ]
      rw [List.ofFn_succ]
      rw [figureOneCoolingQueryBudget]
      have hih := ih (fun i : Fin (N + 1) => f i.succ)
      have hlist : f (Fin.succ 0) :: List.ofFn (fun i => f i.succ.succ) =
          List.ofFn (fun i => f i.succ) := by
        rw [List.ofFn_succ]
      rw [hlist]
      rw [hih, Fin.sum_univ_succ]
      congr 1

theorem figureOneCoolingQueryBudget_explicit (q : VolumeParams) :
    figureOneCoolingQueryBudget q
        (explicitVolumeCoolingSchedule q).variances =
      ∑ k ∈ Finset.range (terminalPhaseSteps q),
        figureOnePhaseSampleCount q (scheduleValue q k) *
          figureOneWalkSteps q (scheduleValue q k) := by
  simp only [explicitVolumeCoolingSchedule, explicitScheduleVariances]
  rw [figureOneCoolingQueryBudget_ofFn]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Finset.mem_range.mp hk]

theorem figureOneWalkSteps_cast_le (q : VolumeParams) (sigma2 : ℝ) :
    (figureOneWalkSteps q sigma2 : ℝ) ≤
      10 ^ 16 * max 1 sigma2 * (q.n : ℝ) ^ 2 *
        protectedLog ((q.n : ℝ) / q.eps) ^ 2 + 1 := by
  unfold figureOneWalkSteps
  have hnonneg : 0 ≤ 10 ^ 16 * max 1 sigma2 * (q.n : ℝ) ^ 2 *
      protectedLog ((q.n : ℝ) / q.eps) ^ 2 := by positivity
  exact (Nat.ceil_lt_add_one hnonneg).le

theorem figureOneWalkSteps_eq_one_of_le_one (q : VolumeParams) {sigma2 : ℝ}
    (hsigma2 : sigma2 ≤ 1) :
    figureOneWalkSteps q sigma2 = figureOneWalkSteps q 1 := by
  unfold figureOneWalkSteps
  rw [max_eq_left hsigma2]
  simp

theorem sum_fixedPhaseWalkSteps_le (q : VolumeParams) :
    ∑ k ∈ Finset.range (terminalPhaseSteps q),
        (if scheduleValue q k ≤ 1 then
          figureOneWalkSteps q (scheduleValue q k) else 0) ≤
      slowPhaseSteps q * figureOneWalkSteps q 1 := by
  classical
  let fixedIndices := (Finset.range (terminalPhaseSteps q)).filter
    fun k => scheduleValue q k ≤ 1
  have hsubset : fixedIndices ⊆ Finset.range (slowPhaseSteps q) := by
    intro k hk
    have hfixed : scheduleValue q k ≤ 1 := (Finset.mem_filter.mp hk).2
    exact Finset.mem_range.mpr (scheduleValue_le_one_imp_lt_slowPhaseSteps q hfixed)
  have hwalk : ∀ k ∈ fixedIndices,
      figureOneWalkSteps q (scheduleValue q k) = figureOneWalkSteps q 1 := by
    intro k hk
    exact figureOneWalkSteps_eq_one_of_le_one q (Finset.mem_filter.mp hk).2
  calc
    ∑ k ∈ Finset.range (terminalPhaseSteps q),
        (if scheduleValue q k ≤ 1 then
          figureOneWalkSteps q (scheduleValue q k) else 0) =
        ∑ k ∈ fixedIndices, figureOneWalkSteps q (scheduleValue q k) := by
      change (∑ k ∈ Finset.range (terminalPhaseSteps q),
          if scheduleValue q k ≤ 1 then
            figureOneWalkSteps q (scheduleValue q k) else 0) =
        ∑ k ∈ (Finset.range (terminalPhaseSteps q)).filter
          (fun k => scheduleValue q k ≤ 1),
            figureOneWalkSteps q (scheduleValue q k)
      rw [Finset.sum_filter]
    _ = fixedIndices.card * figureOneWalkSteps q 1 := by
      rw [Finset.sum_congr rfl hwalk]
      simp
    _ ≤ slowPhaseSteps q * figureOneWalkSteps q 1 := by
      have hcard : fixedIndices.card ≤ slowPhaseSteps q := by
        simpa using Finset.card_le_card hsubset
      exact Nat.mul_le_mul_right _ hcard

theorem sum_figureOneWalkSteps_explicit_le (q : VolumeParams) :
    ((∑ k ∈ Finset.range (terminalPhaseSteps q),
        figureOneWalkSteps q (scheduleValue q k) : ℕ) : ℝ) ≤
      10 ^ 16 * (q.n : ℝ) ^ 2 *
          protectedLog ((q.n : ℝ) / q.eps) ^ 2 *
        ((terminalPhaseSteps q : ℝ) +
          4 * terminalVariance q * protectedLog (terminalVariance q) +
          terminalVariance q) +
        (terminalPhaseSteps q : ℝ) := by
  rw [Nat.cast_sum]
  have hterm :
      (∑ k ∈ Finset.range (terminalPhaseSteps q),
          (figureOneWalkSteps q (scheduleValue q k) : ℝ)) ≤
        ∑ k ∈ Finset.range (terminalPhaseSteps q),
          (10 ^ 16 * (q.n : ℝ) ^ 2 *
              protectedLog ((q.n : ℝ) / q.eps) ^ 2 *
                max 1 (scheduleValue q k) + 1) := by
    apply Finset.sum_le_sum
    intro k hk
    have h := figureOneWalkSteps_cast_le q (scheduleValue q k)
    nlinarith
  calc
    (∑ k ∈ Finset.range (terminalPhaseSteps q),
        (figureOneWalkSteps q (scheduleValue q k) : ℝ)) ≤ _ := hterm
    _ = 10 ^ 16 * (q.n : ℝ) ^ 2 *
          protectedLog ((q.n : ℝ) / q.eps) ^ 2 *
            (∑ k ∈ Finset.range (terminalPhaseSteps q),
              max 1 (scheduleValue q k)) +
          (terminalPhaseSteps q : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      gcongr
      exact sum_scheduleValue_max_le q

theorem dimension_le_terminalVariance (q : VolumeParams) :
    (q.n : ℝ) ≤ terminalVariance q := by
  unfold terminalVariance volumeTerminalScale
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem protectedLog_dimension_le_terminal (q : VolumeParams) :
    protectedLog (q.n : ℝ) ≤ protectedLog (terminalVariance q) := by
  unfold protectedLog
  apply max_le_max_left
  apply Real.strictMonoOn_log.monotoneOn
  · change 0 < (q.n : ℝ)
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) q.dim_ok)
  · change 0 < terminalVariance q
    exact lt_of_lt_of_le (by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) q.dim_ok))
      (dimension_le_terminalVariance q)
  · exact dimension_le_terminalVariance q

theorem protectedLog_dimension_div_eps_le (q : VolumeParams) :
    protectedLog ((q.n : ℝ) / q.eps) ≤
      2 * protectedLog (1 / q.eps) *
        protectedLog (terminalVariance q) := by
  let Ln := protectedLog (q.n : ℝ)
  let Le := protectedLog (1 / q.eps)
  let Lt := protectedLog (terminalVariance q)
  have hLn : 1 ≤ Ln := le_max_left _ _
  have hLe : 1 ≤ Le := le_max_left _ _
  have hLt : 1 ≤ Lt := le_max_left _ _
  have hLnLt : Ln ≤ Lt := by
    simpa [Ln, Lt] using protectedLog_dimension_le_terminal q
  have hlog : Real.log ((q.n : ℝ) / q.eps) ≤ Ln + Le := by
    have hn0 : (q.n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by omega : 0 < 3) q.dim_ok))
    have he0 : 1 / q.eps ≠ 0 := one_div_ne_zero q.heps.1.ne'
    rw [show (q.n : ℝ) / q.eps = (q.n : ℝ) * (1 / q.eps) by ring,
      Real.log_mul hn0 he0]
    exact add_le_add (le_max_right _ _) (le_max_right _ _)
  have hprotected : protectedLog ((q.n : ℝ) / q.eps) ≤ Ln + Le := by
    unfold protectedLog
    apply max_le
    · linarith
    · exact hlog
  have hsum : Ln + Le ≤ 2 * Le * Lt := by
    have h₁ : Ln ≤ Le * Lt := hLnLt.trans <| by
      nlinarith [mul_nonneg (sub_nonneg.mpr hLe) (le_trans zero_le_one hLt)]
    have h₂ : Le ≤ Le * Lt := by
      nlinarith [mul_nonneg (le_trans zero_le_one hLe) (sub_nonneg.mpr hLt)]
    linarith
  exact hprotected.trans hsum

theorem terminalVariance_le_roundness_scale (q : VolumeParams) :
    terminalVariance q ≤
      16384 * max 1 q.roundness * (q.n : ℝ) *
        protectedLog (1 / q.eps) ^ 2 := by
  let n : ℝ := q.n
  let M : ℝ := max 1 q.roundness
  let Le : ℝ := protectedLog (1 / q.eps)
  have hn : 3 ≤ n := by
    dsimp [n]
    exact_mod_cast q.dim_ok
  have hM : 1 ≤ M := le_max_left _ _
  have hLe : 1 ≤ Le := le_max_left _ _
  have hr : q.roundness ≤ M := le_max_right _ _
  have hL8 : protectedLog (8 / q.eps) ≤ 4 * Le := by
    simpa [Le] using protectedLog_eight_div_eps_le_four q
  have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
    intro a b ha hb
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  unfold terminalVariance volumeTerminalScale
  apply max_le
  · have : 1 ≤ M * n * Le ^ 2 := by
      have hn' : 1 ≤ n := le_trans (by norm_num) hn
      exact hmul (hmul hM hn') (one_le_pow₀ hLe)
    dsimp [n, M, Le] at this ⊢
    nlinarith
  · apply max_le
    · have hfactor : 1 ≤ 16384 * M * Le ^ 2 := by
        exact hmul (hmul (by norm_num) hM) (one_le_pow₀ hLe)
      dsimp [n, M, Le] at hfactor ⊢
      nlinarith [mul_nonneg (le_trans (by norm_num) hn)
        (sub_nonneg.mpr hfactor)]
    · have hn0 : 0 ≤ n := le_trans (by norm_num) hn
      have hLe0 : 0 ≤ Le ^ 2 := sq_nonneg _
      have hround := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr hn0) hLe0
      have hL8sq : protectedLog (8 / q.eps) ^ 2 ≤ 16 * Le ^ 2 := by
        have hL80 : 0 ≤ protectedLog (8 / q.eps) :=
          le_trans zero_le_one (le_max_left _ _)
        have hsum0 : 0 ≤ 4 * Le + protectedLog (8 / q.eps) := by positivity
        nlinarith [mul_nonneg (sub_nonneg.mpr hL8) hsum0]
      have hcoef : 0 ≤ 1024 * q.roundness * n :=
        mul_nonneg (mul_nonneg (by norm_num) q.roundness_pos.le) hn0
      have hscale := mul_le_mul_of_nonneg_left hL8sq hcoef
      have hroundScaled := mul_le_mul_of_nonneg_left hround
        (by norm_num : (0 : ℝ) ≤ 16384)
      dsimp [n, M, Le] at hscale hroundScaled ⊢
      nlinarith

theorem terminalPhaseSteps_cast_le (q : VolumeParams) :
    (terminalPhaseSteps q : ℝ) ≤
      15 * (q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps) +
      49153 * max 1 q.roundness * (q.n : ℝ) *
        protectedLog (1 / q.eps) ^ 2 := by
  let n : ℝ := q.n
  let M : ℝ := max 1 q.roundness
  let L : ℝ := protectedLog (n / q.eps)
  let Le : ℝ := protectedLog (1 / q.eps)
  let T : ℝ := terminalVariance q
  let N₁ : ℕ := slowPhaseSteps q
  let N₂ : ℕ := fastPhaseSteps q
  have hn : 3 ≤ n := by
    dsimp [n]
    exact_mod_cast q.dim_ok
  have hM : 1 ≤ M := le_max_left _ _
  have hL : 1 ≤ L := le_max_left _ _
  have hLe : 1 ≤ Le := le_max_left _ _
  have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
    intro a b ha hb
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hN₁raw : (N₁ : ℝ) < 2 * n * (6 + L) + 1 := by
    have hnonneg : 0 ≤ 2 * n * (6 + L) := by positivity
    simpa [N₁, slowPhaseSteps, n, L] using Nat.ceil_lt_add_one hnonneg
  have hN₁ : (N₁ : ℝ) ≤ 15 * n * L := by
    have h6 : 6 + L ≤ 7 * L := by linarith
    have hnL : 1 ≤ n * L := by
      exact hmul (le_trans (by norm_num) hn) hL
    nlinarith
  have hN₂raw : (N₂ : ℝ) < 3 * T + 1 := by
    have hnonneg : 0 ≤ 3 * T := by
      exact mul_nonneg (by norm_num) (le_trans zero_le_one (by
        simpa [T] using terminalVariance_ge_one' q))
    simpa [N₂, fastPhaseSteps, T] using Nat.ceil_lt_add_one hnonneg
  have hT : T ≤ 16384 * M * n * Le ^ 2 := by
    simpa [T, M, n, Le] using terminalVariance_le_roundness_scale q
  have hbase : 1 ≤ M * n * Le ^ 2 := by
    have hn1 : 1 ≤ n := le_trans (by norm_num) hn
    exact hmul (hmul hM hn1) (one_le_pow₀ hLe)
  have hN₂ : (N₂ : ℝ) ≤ 49153 * M * n * Le ^ 2 := by
    nlinarith
  have hstop := terminalPhaseSteps_le_total q
  have hcast : (terminalPhaseSteps q : ℝ) ≤ (N₁ : ℝ) + (N₂ : ℝ) := by
    have hstop' : terminalPhaseSteps q ≤ N₁ + N₂ := by
      simpa [totalPhaseSteps, N₁, N₂] using hstop
    exact_mod_cast hstop'
  dsimp [n, M, L, Le] at hcast hN₁ hN₂ ⊢
  linarith

theorem total_figureOneWalkSteps_cast_le (q : VolumeParams) :
    (((∑ k ∈ Finset.range (terminalPhaseSteps q),
          figureOneWalkSteps q (scheduleValue q k)) +
        figureOneWalkSteps q (terminalVariance q) : ℕ) : ℝ) ≤
      10 ^ 16 * (q.n : ℝ) ^ 2 *
          protectedLog ((q.n : ℝ) / q.eps) ^ 2 *
        (31 * (q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps) +
          196611 * max 1 q.roundness * (q.n : ℝ) *
            protectedLog (1 / q.eps) ^ 2 *
            protectedLog (terminalVariance q)) := by
  let n : ℝ := q.n
  let M : ℝ := max 1 q.roundness
  let L : ℝ := protectedLog (n / q.eps)
  let Le : ℝ := protectedLog (1 / q.eps)
  let H : ℝ := protectedLog (terminalVariance q)
  let T : ℝ := terminalVariance q
  let N : ℝ := terminalPhaseSteps q
  let A : ℝ := 10 ^ 16 * n ^ 2 * L ^ 2
  have hn : 3 ≤ n := by
    dsimp [n]
    exact_mod_cast q.dim_ok
  have hM : 1 ≤ M := le_max_left _ _
  have hL : 1 ≤ L := le_max_left _ _
  have hLe : 1 ≤ Le := le_max_left _ _
  have hH : 1 ≤ H := le_max_left _ _
  have hN : N ≤ 15 * n * L + 49153 * M * n * Le ^ 2 := by
    simpa [N, n, M, L, Le] using terminalPhaseSteps_cast_le q
  have hT : T ≤ 16384 * M * n * Le ^ 2 := by
    simpa [T, n, M, Le] using terminalVariance_le_roundness_scale q
  have hnL : 1 ≤ n * L := by
    have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
      intro a b ha hb
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
    exact hmul (le_trans (by norm_num) hn) hL
  have hbase0 : 0 ≤ M * n * Le ^ 2 := by positivity
  have hTH : T * H ≤ 16384 * M * n * Le ^ 2 * H :=
    mul_le_mul_of_nonneg_right hT (le_trans zero_le_one hH)
  have haggregate : N + 4 * T * H + 2 * T ≤
      15 * n * L + 147457 * M * n * Le ^ 2 * H := by
    have hbaseH : M * n * Le ^ 2 ≤ M * n * Le ^ 2 * H := by
      nlinarith [mul_nonneg hbase0 (sub_nonneg.mpr hH)]
    nlinarith
  have hremainder : N + 1 ≤
      16 * n * L + 49153 * M * n * Le ^ 2 * H := by
    have hbaseH : M * n * Le ^ 2 ≤ M * n * Le ^ 2 * H := by
      nlinarith [mul_nonneg hbase0 (sub_nonneg.mpr hH)]
    linarith
  have hA : 1 ≤ A := by
    dsimp [A]
    have hn1 : 1 ≤ n := le_trans (by norm_num) hn
    have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
      intro a b ha hb
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
    exact hmul (hmul (by norm_num) (one_le_pow₀ hn1)) (one_le_pow₀ hL)
  have hsum := sum_figureOneWalkSteps_explicit_le q
  have hfinal := figureOneWalkSteps_cast_le q (terminalVariance q)
  change ((∑ k ∈ Finset.range (terminalPhaseSteps q),
      figureOneWalkSteps q (scheduleValue q k) : ℕ) : ℝ) ≤
    A * (N + 4 * T * H + T) + N at hsum
  have hfinal' : (figureOneWalkSteps q (terminalVariance q) : ℝ) ≤ A * T + 1 := by
    calc
      (figureOneWalkSteps q (terminalVariance q) : ℝ) ≤
          10 ^ 16 * max 1 (terminalVariance q) * (q.n : ℝ) ^ 2 *
            protectedLog ((q.n : ℝ) / q.eps) ^ 2 + 1 := hfinal
      _ = A * T + 1 := by
        rw [max_eq_right (terminalVariance_ge_one' q)]
        dsimp [A, T, n, L]
        ring
  rw [Nat.cast_add]
  calc
    ((∑ k ∈ Finset.range (terminalPhaseSteps q),
        figureOneWalkSteps q (scheduleValue q k) : ℕ) : ℝ) +
          (figureOneWalkSteps q (terminalVariance q) : ℝ) ≤
        A * (N + 4 * T * H + 2 * T) + (N + 1) := by
      linarith
    _ ≤ A * (15 * n * L + 147457 * M * n * Le ^ 2 * H) +
          (16 * n * L + 49153 * M * n * Le ^ 2 * H) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left haggregate (le_trans zero_le_one hA))
        hremainder
    _ ≤ A * (31 * n * L + 196611 * M * n * Le ^ 2 * H) := by
      have hrem_nonneg : 0 ≤ 16 * n * L + 49153 * M * n * Le ^ 2 * H := by
        positivity
      have hremA : 16 * n * L + 49153 * M * n * Le ^ 2 * H ≤
          A * (16 * n * L + 49153 * M * n * Le ^ 2 * H) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hA) hrem_nonneg]
      calc
        _ ≤ A * (15 * n * L + 147457 * M * n * Le ^ 2 * H) +
            A * (16 * n * L + 49153 * M * n * Le ^ 2 * H) :=
          by gcongr
        _ ≤ A * (31 * n * L + 196611 * M * n * Le ^ 2 * H) := by
          have hnonneg : 0 ≤ A * (M * n * Le ^ 2 * H) := by positivity
          nlinarith
    _ = _ := by
      dsimp [A, n, M, L, Le, H]

/-- The concrete Figure-1 base run obeys the exact unrestricted polylogarithmic
query rate. -/
theorem figureOne_base_query_cost_sharp (q : VolumeParams) :
    1 + (figureOneCoolingQueryBudget q
            (explicitVolumeCoolingSchedule q).variances +
          figureOneSampleCount q *
            figureOneWalkSteps q (terminalVariance q)) ≤
      Nat.ceil ((2 * 10 ^ 24) * volumeBaseComplexityRate q) := by
  let n : ℝ := q.n
  let M : ℝ := max 1 q.roundness
  let L : ℝ := protectedLog (n / q.eps)
  let Le : ℝ := protectedLog (1 / q.eps)
  let H : ℝ := protectedLog (terminalVariance q)
  let R : ℝ := M * n ^ 3 / q.eps ^ 2 * Le ^ 2 * L ^ 2 * H ^ 2
  let W : ℕ :=
    (∑ k ∈ Finset.range (terminalPhaseSteps q),
      figureOneWalkSteps q (scheduleValue q k)) +
      figureOneWalkSteps q (terminalVariance q)
  have hn : 3 ≤ n := by
    dsimp [n]
    exact_mod_cast q.dim_ok
  have hM : 1 ≤ M := le_max_left _ _
  have hL : 1 ≤ L := le_max_left _ _
  have hLe : 1 ≤ Le := le_max_left _ _
  have hH : 1 ≤ H := le_max_left _ _
  have he2pos : 0 < q.eps ^ 2 := sq_pos_of_pos q.heps.1
  have he2le : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  have hR : 1 ≤ R := by
    have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ (le_trans (by norm_num) hn)
    have hfirst : 1 ≤ M * n ^ 3 / q.eps ^ 2 := by
      rw [le_div_iff₀ he2pos]
      simpa only [one_mul] using he2le.trans (by
        have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
          intro a b ha hb
          nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
        exact hmul hM hn3)
    have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
      intro a b ha hb
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
    exact hmul (hmul (hmul hfirst (one_le_pow₀ hLe))
      (one_le_pow₀ hL)) (one_le_pow₀ hH)
  have hsample : (figureOneSampleCount q : ℝ) ≤ 513 * H / q.eps ^ 2 := by
    have hraw_nonneg : 0 ≤ 512 * H / q.eps ^ 2 := by positivity
    have hceil := Nat.ceil_lt_add_one hraw_nonneg
    change (figureOneSampleCount q : ℝ) <
      512 * H / q.eps ^ 2 + 1 at hceil
    have hone : 1 ≤ H / q.eps ^ 2 := by
      rw [le_div_iff₀ he2pos]
      simpa only [one_mul] using he2le.trans hH
    rw [show 513 * H / q.eps ^ 2 =
      512 * H / q.eps ^ 2 + H / q.eps ^ 2 by ring]
    linarith
  have hwalk : (W : ℝ) ≤
      10 ^ 16 * n ^ 2 * L ^ 2 *
        (31 * n * L + 196611 * M * n * Le ^ 2 * H) := by
    simpa [W, n, M, L, Le, H] using total_figureOneWalkSteps_cast_le q
  have hLbound : L ≤ 2 * Le * H := by
    simpa [L, Le, H, n] using protectedLog_dimension_div_eps_le q
  have hslow : n ^ 3 / q.eps ^ 2 * L ^ 3 * H ≤ 2 * R := by
    calc
      n ^ 3 / q.eps ^ 2 * L ^ 3 * H =
          (n ^ 3 / q.eps ^ 2 * L ^ 2 * H) * L := by ring
      _ ≤ (n ^ 3 / q.eps ^ 2 * L ^ 2 * H) * (2 * Le * H) := by
        gcongr
      _ ≤ 2 * R := by
        have hME : 1 ≤ M * Le := by
          have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
            intro a b ha hb
            nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
          exact hmul hM hLe
        have hnonneg : 0 ≤ n ^ 3 / q.eps ^ 2 * Le * L ^ 2 * H ^ 2 := by
          positivity
        rw [show (n ^ 3 / q.eps ^ 2 * L ^ 2 * H) * (2 * Le * H) =
            2 * (n ^ 3 / q.eps ^ 2 * Le * L ^ 2 * H ^ 2) by ring,
          show 2 * R = 2 *
            ((n ^ 3 / q.eps ^ 2 * Le * L ^ 2 * H ^ 2) * (M * Le)) by
              dsimp [R]
              ring]
        have hX : n ^ 3 / q.eps ^ 2 * Le * L ^ 2 * H ^ 2 ≤
            (n ^ 3 / q.eps ^ 2 * Le * L ^ 2 * H ^ 2) * (M * Le) := by
          nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hME)]
        linarith
  have hproduct :
      (figureOneSampleCount q : ℝ) * (W : ℝ) ≤
        (100893249 * 10 ^ 16) * R := by
    have hsample0 : 0 ≤ (figureOneSampleCount q : ℝ) := by positivity
    have hW0 : 0 ≤ (W : ℝ) := by positivity
    calc
      (figureOneSampleCount q : ℝ) * (W : ℝ) ≤
          (513 * H / q.eps ^ 2) *
            (10 ^ 16 * n ^ 2 * L ^ 2 *
              (31 * n * L + 196611 * M * n * Le ^ 2 * H)) :=
        mul_le_mul hsample hwalk hW0 (by positivity)
      _ = 513 * 10 ^ 16 *
          (31 * (n ^ 3 / q.eps ^ 2 * L ^ 3 * H) + 196611 * R) := by
        dsimp [R]
        ring
      _ ≤ 513 * 10 ^ 16 * (31 * (2 * R) + 196611 * R) := by
        gcongr
      _ = (100893249 * 10 ^ 16) * R := by ring
  have hfixedSample : (figureOneFixedSampleCount q : ℝ) ≤
      4097 * L / q.eps ^ 2 := by
    have hraw_nonneg : 0 ≤ 4096 * L / q.eps ^ 2 := by positivity
    have hceil := Nat.ceil_lt_add_one hraw_nonneg
    change (figureOneFixedSampleCount q : ℝ) <
      4096 * L / q.eps ^ 2 + 1 at hceil
    have hone : 1 ≤ L / q.eps ^ 2 := by
      rw [le_div_iff₀ he2pos]
      simpa only [one_mul] using he2le.trans hL
    rw [show 4097 * L / q.eps ^ 2 =
      4096 * L / q.eps ^ 2 + L / q.eps ^ 2 by ring]
    linarith
  have hslowSteps : (slowPhaseSteps q : ℝ) ≤ 15 * n * L := by
    have hraw_nonneg : 0 ≤ 2 * n * (6 + L) := by positivity
    have hceil := Nat.ceil_lt_add_one hraw_nonneg
    change (slowPhaseSteps q : ℝ) < 2 * n * (6 + L) + 1 at hceil
    have hnL : 1 ≤ n * L := by nlinarith
    have h6 : 6 + L ≤ 7 * L := by linarith
    dsimp [slowPhaseSteps, n, L] at hceil ⊢
    nlinarith [mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ 2 * n)]
  have hwalkOne : (figureOneWalkSteps q 1 : ℝ) ≤
      2 * 10 ^ 16 * n ^ 2 * L ^ 2 := by
    have h := figureOneWalkSteps_cast_le q 1
    have h' : (figureOneWalkSteps q 1 : ℝ) ≤
        10 ^ 16 * n ^ 2 * L ^ 2 + 1 := by
      simpa only [max_self, mul_one] using h
    have hbase : 1 ≤ 10 ^ 16 * n ^ 2 * L ^ 2 := by
      have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ (le_trans (by norm_num) hn)
      have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
      nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr hL2)]
    exact h'.trans (by nlinarith)
  have hLsq : L ^ 2 ≤ 4 * Le ^ 2 * H ^ 2 := by
    nlinarith [sq_nonneg (2 * Le * H - L),
      mul_nonneg (le_trans zero_le_one hLe) (le_trans zero_le_one hH)]
  have hfixedRate : n ^ 3 / q.eps ^ 2 * L ^ 4 ≤ 4 * R := by
    calc
      n ^ 3 / q.eps ^ 2 * L ^ 4 =
          (n ^ 3 / q.eps ^ 2 * L ^ 2) * L ^ 2 := by ring
      _ ≤ (n ^ 3 / q.eps ^ 2 * L ^ 2) * (4 * Le ^ 2 * H ^ 2) := by
        gcongr
      _ ≤ 4 * R := by
        let X := n ^ 3 / q.eps ^ 2 * L ^ 2 * Le ^ 2 * H ^ 2
        have hnonneg : 0 ≤ X := by
          positivity
        calc
          (n ^ 3 / q.eps ^ 2 * L ^ 2) * (4 * Le ^ 2 * H ^ 2) = 4 * X := by
            dsimp [X]
            ring
          _ ≤ 4 * (M * X) := by
            gcongr
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hnonneg
          _ = 4 * R := by
            dsimp [R, X]
            ring
  have hfixedProduct :
      (figureOneFixedSampleCount q : ℝ) * (slowPhaseSteps q : ℝ) *
          (figureOneWalkSteps q 1 : ℝ) ≤
        (491640 * 10 ^ 16) * R := by
    calc
      (figureOneFixedSampleCount q : ℝ) * (slowPhaseSteps q : ℝ) *
          (figureOneWalkSteps q 1 : ℝ) ≤
        (4097 * L / q.eps ^ 2) * (15 * n * L) *
          (2 * 10 ^ 16 * n ^ 2 * L ^ 2) := by
        gcongr
      _ = 122910 * 10 ^ 16 * (n ^ 3 / q.eps ^ 2 * L ^ 4) := by ring
      _ ≤ 122910 * 10 ^ 16 * (4 * R) := by gcongr
      _ = (491640 * 10 ^ 16) * R := by ring
  have hbudgetUpper :
      figureOneCoolingQueryBudget q
          (explicitVolumeCoolingSchedule q).variances +
        figureOneSampleCount q * figureOneWalkSteps q (terminalVariance q) ≤
      figureOneSampleCount q * W +
        figureOneFixedSampleCount q *
          (slowPhaseSteps q * figureOneWalkSteps q 1) := by
    rw [figureOneCoolingQueryBudget_explicit]
    have hterm : ∀ k ∈ Finset.range (terminalPhaseSteps q),
        figureOnePhaseSampleCount q (scheduleValue q k) *
            figureOneWalkSteps q (scheduleValue q k) ≤
          figureOneSampleCount q * figureOneWalkSteps q (scheduleValue q k) +
            figureOneFixedSampleCount q *
              (if scheduleValue q k ≤ 1 then
                figureOneWalkSteps q (scheduleValue q k) else 0) := by
      intro k _
      by_cases hk : scheduleValue q k ≤ 1
      · simp [figureOnePhaseSampleCount, hk]
      · simp [figureOnePhaseSampleCount, hk]
    calc
      (∑ k ∈ Finset.range (terminalPhaseSteps q),
          figureOnePhaseSampleCount q (scheduleValue q k) *
            figureOneWalkSteps q (scheduleValue q k)) +
          figureOneSampleCount q * figureOneWalkSteps q (terminalVariance q) ≤
        (∑ k ∈ Finset.range (terminalPhaseSteps q),
          (figureOneSampleCount q * figureOneWalkSteps q (scheduleValue q k) +
            figureOneFixedSampleCount q *
              (if scheduleValue q k ≤ 1 then
                figureOneWalkSteps q (scheduleValue q k) else 0))) +
          figureOneSampleCount q * figureOneWalkSteps q (terminalVariance q) := by
        gcongr with k hk
        exact hterm k hk
      _ = figureOneSampleCount q * W +
          figureOneFixedSampleCount q *
            (∑ k ∈ Finset.range (terminalPhaseSteps q),
              if scheduleValue q k ≤ 1 then
                figureOneWalkSteps q (scheduleValue q k) else 0) := by
        dsimp [W]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
      _ ≤ figureOneSampleCount q * W +
          figureOneFixedSampleCount q *
            (slowPhaseSteps q * figureOneWalkSteps q 1) := by
        gcongr
        exact sum_fixedPhaseWalkSteps_le q
  have hreal :
      ((1 + (figureOneCoolingQueryBudget q
              (explicitVolumeCoolingSchedule q).variances +
            figureOneSampleCount q *
              figureOneWalkSteps q (terminalVariance q)) : ℕ) : ℝ) ≤
        (2 * 10 ^ 24) * volumeBaseComplexityRate q := by
    have hbudgetCast :
        (((figureOneCoolingQueryBudget q
            (explicitVolumeCoolingSchedule q).variances +
          figureOneSampleCount q *
            figureOneWalkSteps q (terminalVariance q) : ℕ) : ℝ)) ≤
          (figureOneSampleCount q : ℝ) * (W : ℝ) +
            (figureOneFixedSampleCount q : ℝ) *
              ((slowPhaseSteps q : ℝ) * (figureOneWalkSteps q 1 : ℝ)) := by
      exact_mod_cast hbudgetUpper
    rw [Nat.cast_add, Nat.cast_one]
    have hconstant : (101384889 : ℝ) * 10 ^ 16 + 1 ≤ 2 * 10 ^ 24 := by norm_num
    have hleft : 1 +
        ((figureOneCoolingQueryBudget q
            (explicitVolumeCoolingSchedule q).variances +
          figureOneSampleCount q *
            figureOneWalkSteps q (terminalVariance q) : ℕ) : ℝ) ≤
        ((101384889 : ℝ) * 10 ^ 16 + 1) * R := by
      have hfixedProduct' :
          (figureOneFixedSampleCount q : ℝ) *
              ((slowPhaseSteps q : ℝ) * (figureOneWalkSteps q 1 : ℝ)) ≤
            (491640 * 10 ^ 16) * R := by
        simpa [mul_assoc] using hfixedProduct
      calc
        _ ≤ 1 + ((figureOneSampleCount q : ℝ) * (W : ℝ) +
            (figureOneFixedSampleCount q : ℝ) *
              ((slowPhaseSteps q : ℝ) * (figureOneWalkSteps q 1 : ℝ))) := by
          gcongr
        _ ≤ 1 + ((100893249 * 10 ^ 16) * R + (491640 * 10 ^ 16) * R) := by
          simpa [add_comm] using add_le_add_left
            (add_le_add hproduct hfixedProduct') 1
        _ = ((101384889 : ℝ) * 10 ^ 16 + 1) * R - (R - 1) := by ring
        _ ≤ ((101384889 : ℝ) * 10 ^ 16 + 1) * R := by linarith
    have hrate : volumeBaseComplexityRate q = R := by
      dsimp [volumeBaseComplexityRate, R, M, n, Le, L, H, terminalVariance]
    rw [hrate]
    exact hleft.trans <| mul_le_mul_of_nonneg_right hconstant (le_trans zero_le_one hR)
  exact_mod_cast le_trans hreal
    (Nat.le_ceil ((2 * 10 ^ 24) * volumeBaseComplexityRate q))

/-- Convenient decimal envelope used by the public existential statement. -/
theorem figureOne_base_query_cost_explicit (q : VolumeParams) :
    1 + (figureOneCoolingQueryBudget q
            (explicitVolumeCoolingSchedule q).variances +
          figureOneSampleCount q *
            figureOneWalkSteps q (terminalVariance q)) ≤
      Nat.ceil (10 ^ 25 * volumeBaseComplexityRate q) := by
  refine (figureOne_base_query_cost_sharp q).trans (Nat.ceil_mono ?_)
  have hrate : 0 ≤ volumeBaseComplexityRate q := by
    unfold volumeBaseComplexityRate
    positivity
  nlinarith

theorem figureOne_base_query_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ q : VolumeParams,
      1 + (figureOneCoolingQueryBudget q
              (explicitVolumeCoolingSchedule q).variances +
            figureOneSampleCount q *
              figureOneWalkSteps q (terminalVariance q)) ≤
        Nat.ceil (C * volumeBaseComplexityRate q) := by
  exact ⟨10 ^ 25, by positivity, figureOne_base_query_cost_explicit⟩

end ArlibCommunity.Algorithms.CV18
