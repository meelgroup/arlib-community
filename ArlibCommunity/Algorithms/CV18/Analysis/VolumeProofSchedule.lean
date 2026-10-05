/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Pseudocode
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.List.ChainOfFn

open Function

namespace ArlibCommunity.Algorithms.CV18

theorem protectedLog_eight_div_eps_le_four (q : VolumeParams) :
    protectedLog (8 / q.eps) ≤ 4 * protectedLog (1 / q.eps) := by
  let Le := protectedLog (1 / q.eps)
  have hLe : 1 ≤ Le := le_max_left _ _
  have hlogLe : Real.log (1 / q.eps) ≤ Le := le_max_right _ _
  have hlog8 : Real.log 8 < 3 := by
    rw [show (8 : ℝ) = 2 * 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hlog : Real.log (8 / q.eps) ≤ 4 * Le := by
    rw [show 8 / q.eps = 8 * (1 / q.eps) by ring,
      Real.log_mul (by norm_num) (one_div_ne_zero q.heps.1.ne')]
    linarith
  change max 1 (Real.log (8 / q.eps)) ≤ 4 * Le
  apply max_le
  · linarith
  · exact hlog


theorem initialVariance_pos' (q : VolumeParams) : 0 < initialVariance q := by
  unfold initialVariance
  have hn : 0 < (q.n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) q.dim_ok)
  exact div_pos q.heps.1 (mul_pos (by norm_num) hn)

theorem terminalVariance_ge_one' (q : VolumeParams) : 1 ≤ terminalVariance q := by
  exact le_max_left _ _

theorem initialVariance_lt_one' (q : VolumeParams) : initialVariance q < 1 := by
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  unfold initialVariance
  rw [div_lt_one (by positivity : 0 < 64 * (q.n : ℝ))]
  linarith [q.heps.2]

theorem coolingRate_one_lt' (q : VolumeParams) {s : ℝ} (hs : 0 < s) :
    1 < coolingRate q s := by
  unfold coolingRate
  split_ifs
  · have hn : 0 < (q.n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) q.dim_ok)
    have : 0 < 1 / (q.n : ℝ) := one_div_pos.mpr hn
    linarith
  · have ht : 0 < terminalVariance q := lt_of_lt_of_le zero_lt_one (terminalVariance_ge_one' q)
    have : 0 < s / (2 * terminalVariance q) := div_pos hs (by positivity)
    linarith

theorem nextVariance_pos' (q : VolumeParams) {s : ℝ} (hs : 0 < s) :
    0 < nextVariance q s := by
  unfold nextVariance
  exact lt_min (lt_of_lt_of_le zero_lt_one (terminalVariance_ge_one' q))
    (mul_pos hs (lt_trans zero_lt_one (coolingRate_one_lt' q hs)))

theorem nextVariance_le_terminal' (q : VolumeParams) (s : ℝ) :
    nextVariance q s ≤ terminalVariance q := by
  exact min_le_left _ _

theorem nextVariance_terminal' (q : VolumeParams) :
    nextVariance q (terminalVariance q) = terminalVariance q := by
  unfold nextVariance
  rw [min_eq_left]
  have ht := terminalVariance_ge_one' q
  have hr := (coolingRate_one_lt' q (lt_of_lt_of_le zero_lt_one ht)).le
  nlinarith

theorem nextVariance_ge_self' (q : VolumeParams) {s : ℝ}
    (hs : 0 < s) (hst : s ≤ terminalVariance q) :
    s ≤ nextVariance q s := by
  unfold nextVariance
  refine le_min hst ?_
  have hr := (coolingRate_one_lt' q hs).le
  nlinarith

noncomputable def scheduleValue (q : VolumeParams) (k : ℕ) : ℝ :=
  (nextVariance q)^[k] (initialVariance q)

theorem scheduleValue_succ (q : VolumeParams) (k : ℕ) :
    scheduleValue q (k + 1) = nextVariance q (scheduleValue q k) := by
  simp [scheduleValue, Function.iterate_succ_apply']

theorem scheduleValue_pos (q : VolumeParams) : ∀ k, 0 < scheduleValue q k := by
  intro k
  induction k with
  | zero => simpa [scheduleValue] using initialVariance_pos' q
  | succ k ih => simpa [scheduleValue_succ] using nextVariance_pos' q ih

theorem scheduleValue_le_terminal (q : VolumeParams) :
    ∀ k, scheduleValue q k ≤ terminalVariance q := by
  intro k
  cases k with
  | zero => exact le_trans (initialVariance_lt_one' q).le (terminalVariance_ge_one' q)
  | succ k => simpa [scheduleValue_succ] using nextVariance_le_terminal' q (scheduleValue q k)

theorem scheduleValue_mono (q : VolumeParams) : Monotone (scheduleValue q) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [scheduleValue_succ]
  exact nextVariance_ge_self' q (scheduleValue_pos q k) (scheduleValue_le_terminal q k)

theorem scheduleValue_terminal_persists (q : VolumeParams) {i j : ℕ}
    (hij : i ≤ j) (hi : scheduleValue q i = terminalVariance q) :
    scheduleValue q j = terminalVariance q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h : ∀ d, scheduleValue q (i + d) = terminalVariance q := by
    intro d
    induction d with
    | zero => simpa using hi
    | succ d ih =>
        rw [Nat.add_succ, scheduleValue_succ, ih, nextVariance_terminal']
  exact h d

noncomputable def slowPhaseSteps (q : VolumeParams) : ℕ :=
  Nat.ceil (2 * (q.n : ℝ) * (6 + protectedLog ((q.n : ℝ) / q.eps)))

theorem slowPhaseSteps_cast_le (q : VolumeParams) :
    (slowPhaseSteps q : ℝ) ≤
      15 * (q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps) := by
  let n : ℝ := q.n
  let L : ℝ := protectedLog (n / q.eps)
  have hn : 3 ≤ n := by
    dsimp [n]
    exact_mod_cast q.dim_ok
  have hL : 1 ≤ L := le_max_left _ _
  have hraw_nonneg : 0 ≤ 2 * n * (6 + L) := by positivity
  have hceil := Nat.ceil_lt_add_one hraw_nonneg
  change (slowPhaseSteps q : ℝ) < 2 * n * (6 + L) + 1 at hceil
  have hnL : 1 ≤ n * L := by nlinarith
  have h6 : 6 + L ≤ 7 * L := by linarith
  dsimp [slowPhaseSteps, n, L] at hceil ⊢
  nlinarith [mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ 2 * n)]

theorem slowPhase_power_gt (q : VolumeParams) :
    1 < initialVariance q *
      (1 + 1 / (q.n : ℝ)) ^ slowPhaseSteps q := by
  let n : ℝ := q.n
  let e : ℝ := q.eps
  let a : ℝ := initialVariance q
  let b : ℝ := 1 + 1 / n
  let L : ℝ := protectedLog (n / e)
  let N : ℕ := slowPhaseSteps q
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) q.dim_ok)
  have he : 0 < e := q.heps.1
  have ha : 0 < a := initialVariance_pos' q
  have hb : 0 < b := by dsimp [b]; positivity
  have hne : 0 < n / e := div_pos hn he
  have hL : Real.log (n / e) ≤ L := by exact le_max_right _ _
  have hlog2 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_one_gt_two
  have hlog64 : Real.log 64 < 6 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
    linarith
  have h_inv_a : 1 / a = 64 * (n / e) := by
    dsimp [a, initialVariance, n, e]
    field_simp
  have hlog_inv : Real.log (1 / a) < 6 + L := by
    rw [h_inv_a, Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) (ne_of_gt hne)]
    linarith
  have hlogb_lower : 1 / (2 * n) ≤ Real.log b := by
    have hraw := Real.le_log_one_add_of_nonneg (show 0 ≤ 1 / n by positivity)
    dsimp [b] at hraw ⊢
    have hn3 : 3 ≤ n := by
      change (3 : ℝ) ≤ (q.n : ℝ)
      exact_mod_cast q.dim_ok
    have hcmp : 1 / (2 * n) ≤ 2 * (1 / n) / (1 / n + 2) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * n) (by positivity : 0 < 1 / n + 2)]
      field_simp
      nlinarith
    exact hcmp.trans hraw
  have hN : 2 * n * (6 + L) ≤ (N : ℝ) := by
    dsimp [N, slowPhaseSteps, n, e, L]
    exact Nat.le_ceil _
  have hlogpow : Real.log (1 / a) < (N : ℝ) * Real.log b := by
    have hnonnegN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have hnonnegX : 0 ≤ 2 * n * (6 + L) := by
      have : 1 ≤ L := le_max_left _ _
      positivity
    have hmul := mul_le_mul hN hlogb_lower (by positivity : 0 ≤ 1 / (2*n)) hnonnegN
    have hcalc : 6 + L ≤ (N : ℝ) * Real.log b := by
      calc
        6 + L = (2 * n * (6 + L)) * (1 / (2 * n)) := by field_simp
        _ ≤ (N : ℝ) * Real.log b := hmul
    exact lt_of_lt_of_le hlog_inv hcalc
  have hpow : 1 / a < b ^ N := Real.lt_pow_of_log_lt hb hlogpow
  calc
    1 = a * (1 / a) := by field_simp
    _ < a * b ^ N := by
      have hpos : 0 < a * (b ^ N - 1 / a) := mul_pos ha (sub_pos.mpr hpow)
      nlinarith
    _ = initialVariance q * (1 + 1 / (q.n : ℝ)) ^ slowPhaseSteps q := by
      rfl

theorem slowPhase_reaches_one_or_terminal (q : VolumeParams) :
    scheduleValue q (slowPhaseSteps q) = terminalVariance q ∨
      1 < scheduleValue q (slowPhaseSteps q) := by
  by_contra h
  push Not at h
  obtain ⟨hnot, hle⟩ := h
  let N := slowPhaseSteps q
  let a := initialVariance q
  let b := 1 + 1 / (q.n : ℝ)
  have hformula : ∀ k ≤ N, scheduleValue q k = a * b ^ k := by
    intro k hk
    induction k with
    | zero => simp [scheduleValue, a]
    | succ k ih =>
        have hkN : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
        have hnext_le : scheduleValue q (k + 1) ≤ scheduleValue q N :=
          scheduleValue_mono q hk
        have hnext_not : scheduleValue q (k + 1) ≠ terminalVariance q := by
          intro heq
          exact hnot (scheduleValue_terminal_persists q hk heq)
        rw [scheduleValue_succ]
        unfold nextVariance
        have hmin : min (terminalVariance q)
            (scheduleValue q k * coolingRate q (scheduleValue q k)) ≠
            terminalVariance q := by
          rwa [scheduleValue_succ] at hnext_not
        rw [min_def] at hmin ⊢
        split_ifs at hmin ⊢ with hcap
        · exact (hmin rfl).elim
        · rw [coolingRate, if_pos]
          · rw [ih hkN, pow_succ]
            dsimp [b]
            ring
          · exact le_trans (scheduleValue_mono q (Nat.le_succ k)) (le_trans hnext_le hle)
  have hfinal := hformula N le_rfl
  have hgrow := slowPhase_power_gt q
  rw [hfinal] at hle
  exact (not_lt_of_ge hle) (by simpa [a, b, N] using hgrow)

theorem scheduleValue_le_one_imp_lt_slowPhaseSteps (q : VolumeParams)
    {k : ℕ} (hk : scheduleValue q k ≤ 1) : k < slowPhaseSteps q := by
  have hT : 1 < terminalVariance q := by
    unfold terminalVariance volumeTerminalScale
    have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3)
      (hn.trans (le_trans (le_max_left _ _) (le_max_right _ _)))
  have hslow : 1 < scheduleValue q (slowPhaseSteps q) := by
    rcases slowPhase_reaches_one_or_terminal q with hterminal | hone
    · simpa [hterminal] using hT
    · exact hone
  by_contra hnot
  have hmono := scheduleValue_mono q (Nat.le_of_not_gt hnot)
  linarith

noncomputable def fastPhaseSteps (q : VolumeParams) : ℕ :=
  Nat.ceil (3 * terminalVariance q)

theorem fast_reciprocal_step (q : VolumeParams) {s : ℝ}
    (hs1 : 1 < s) (hst : s ≤ terminalVariance q)
    (hnext : nextVariance q s ≠ terminalVariance q) :
    1 / nextVariance q s ≤ 1 / s - 1 / (3 * terminalVariance q) := by
  let t := terminalVariance q
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (terminalVariance_ge_one' q)
  have hs : 0 < s := lt_trans zero_lt_one hs1
  have hform : nextVariance q s = s * (1 + s / (2 * t)) := by
    unfold nextVariance at hnext ⊢
    rw [min_def] at hnext ⊢
    split_ifs at hnext ⊢ with hcap
    · exact (hnext rfl).elim
    · rw [coolingRate, if_neg (not_le.mpr hs1)]
  rw [hform]
  have hden1 : 0 < s * (1 + s / (2 * t)) := by positivity
  have hden2 : 0 < 3 * t := by positivity
  have h2t : 0 < 2 * t + s := by positivity
  dsimp [t] at *
  field_simp
  nlinarith

theorem schedule_reaches_terminal (q : VolumeParams) :
    scheduleValue q (slowPhaseSteps q + fastPhaseSteps q) = terminalVariance q := by
  rcases slowPhase_reaches_one_or_terminal q with hterminal | hone
  · exact scheduleValue_terminal_persists q (Nat.le_add_right _ _) hterminal
  · by_contra hfinal
    let N₁ := slowPhaseSteps q
    let N₂ := fastPhaseSteps q
    let t := terminalVariance q
    let y : ℕ → ℝ := fun k => scheduleValue q (N₁ + k)
    have ht : 0 < t := lt_of_lt_of_le zero_lt_one (terminalVariance_ge_one' q)
    have hypos : ∀ k, 0 < y k := by
      intro k
      exact scheduleValue_pos q _
    have hyle : ∀ k, y k ≤ t := by
      intro k
      exact scheduleValue_le_terminal q _
    have hyone : ∀ k, 1 < y k := by
      intro k
      exact lt_of_lt_of_le (by simpa [y, N₁] using hone)
        (scheduleValue_mono q (Nat.le_add_right N₁ k))
    have hynot : ∀ k ≤ N₂, y k ≠ t := by
      intro k hk heq
      apply hfinal
      simpa [y, N₁, N₂, t] using
        scheduleValue_terminal_persists q
          (show N₁ + k ≤ N₁ + N₂ by omega) heq
    have hy_succ : ∀ k, y (k + 1) = nextVariance q (y k) := by
      intro k
      dsimp [y]
      rw [show N₁ + (k + 1) = (N₁ + k) + 1 by omega, scheduleValue_succ]
    have hrecip : ∀ k ≤ N₂, 1 / y k ≤ 1 / y 0 - (k : ℝ) / (3 * t) := by
      intro k hk
      induction k with
      | zero => norm_num
      | succ k ih =>
          have hk' : k ≤ N₂ := Nat.le_trans (Nat.le_succ k) hk
          have hstep := fast_reciprocal_step q (hyone k) (hyle k) (by
            rw [← hy_succ]
            exact hynot (k + 1) hk)
          rw [hy_succ]
          calc
            1 / nextVariance q (y k) ≤ 1 / y k - 1 / (3 * t) := hstep
            _ ≤ (1 / y 0 - (k : ℝ) / (3 * t)) - 1 / (3 * t) := by
              linarith [ih hk']
            _ = 1 / y 0 - ((k + 1 : ℕ) : ℝ) / (3 * t) := by
              push_cast
              field_simp
              ring
    have hN₂ : 3 * t ≤ (N₂ : ℝ) := by
      dsimp [N₂, fastPhaseSteps, t]
      exact Nat.le_ceil _
    have hy0inv : 1 / y 0 < 1 := (div_lt_one (hypos 0)).2 (hyone 0)
    have hneg : 1 / y 0 - (N₂ : ℝ) / (3 * t) < 0 := by
      have : 1 ≤ (N₂ : ℝ) / (3 * t) := by
        rw [le_div_iff₀ (by positivity)]
        simpa using hN₂
      linarith
    have := hrecip N₂ le_rfl
    have : 0 < 1 / y N₂ := one_div_pos.mpr (hypos N₂)
    linarith

noncomputable def totalPhaseSteps (q : VolumeParams) : ℕ :=
  slowPhaseSteps q + fastPhaseSteps q

/-! The first index at which the deterministic schedule reaches its terminal
variance.  Using the least such index matters for the runtime proof: after this
point `nextVariance` is stationary, so retaining the coarse upper-bound tail
would add useless terminal-to-terminal sampling phases. -/
noncomputable def terminalPhaseSteps (q : VolumeParams) : ℕ :=
  Nat.find (show ∃ k : ℕ, scheduleValue q k = terminalVariance q from
    ⟨totalPhaseSteps q, by
      simpa [totalPhaseSteps] using schedule_reaches_terminal q⟩)

theorem scheduleValue_terminalPhaseSteps (q : VolumeParams) :
    scheduleValue q (terminalPhaseSteps q) = terminalVariance q := by
  unfold terminalPhaseSteps
  exact Nat.find_spec (show ∃ k : ℕ, scheduleValue q k = terminalVariance q from
    ⟨totalPhaseSteps q, by
      simpa [totalPhaseSteps] using schedule_reaches_terminal q⟩)

theorem terminalPhaseSteps_le_total (q : VolumeParams) :
    terminalPhaseSteps q ≤ totalPhaseSteps q := by
  unfold terminalPhaseSteps
  exact Nat.find_min'
    (show ∃ k : ℕ, scheduleValue q k = terminalVariance q from
      ⟨totalPhaseSteps q, by
        simpa [totalPhaseSteps] using schedule_reaches_terminal q⟩)
    (by simpa [totalPhaseSteps] using schedule_reaches_terminal q)

theorem scheduleValue_ne_terminal_of_lt_terminalPhaseSteps
    (q : VolumeParams) {k : ℕ} (hk : k < terminalPhaseSteps q) :
    scheduleValue q k ≠ terminalVariance q := by
  unfold terminalPhaseSteps at hk
  exact Nat.find_min
    (show ∃ j : ℕ, scheduleValue q j = terminalVariance q from
      ⟨totalPhaseSteps q, by
        simpa [totalPhaseSteps] using schedule_reaches_terminal q⟩) hk

/-- A logarithmic potential which is zero throughout the variance-at-most-one
part and begins telescoping exactly when accelerated cooling starts. -/
noncomputable def scheduleLogPotential (q : VolumeParams) (k : ℕ) : ℝ :=
  Real.log (max 1 (scheduleValue q k))

theorem scheduleLogPotential_mono (q : VolumeParams) :
    Monotone (scheduleLogPotential q) := by
  intro i j hij
  apply Real.strictMonoOn_log.monotoneOn
  · exact lt_of_lt_of_le zero_lt_one
      (le_max_left (1 : ℝ) (scheduleValue q i))
  · exact lt_of_lt_of_le zero_lt_one
      (le_max_left (1 : ℝ) (scheduleValue q j))
  · exact max_le_max_left (1 : ℝ) (scheduleValue_mono q hij)

/-- A nonterminal accelerated step pays for its full current variance, with
no additive slow-phase charge, by the clipped logarithmic potential. -/
theorem scheduleValue_accelerated_charge_to_logPotential
    (q : VolumeParams) {k : ℕ}
    (hk : k + 1 < terminalPhaseSteps q)
    (hsone : 1 < scheduleValue q k) :
    scheduleValue q k ≤
      4 * terminalVariance q *
        (scheduleLogPotential q (k + 1) - scheduleLogPotential q k) := by
  let s := scheduleValue q k
  let t := terminalVariance q
  have hs : 0 < s := scheduleValue_pos q k
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (by
    simpa [t] using terminalVariance_ge_one' q)
  have hst : s ≤ t := scheduleValue_le_terminal q k
  have hnextNot : nextVariance q s ≠ t := by
    simpa [s, t, scheduleValue_succ] using
      scheduleValue_ne_terminal_of_lt_terminalPhaseSteps q hk
  have hnext : nextVariance q s = s * (1 + s / (2 * t)) := by
    unfold nextVariance at hnextNot ⊢
    rw [min_def] at hnextNot ⊢
    split_ifs at hnextNot ⊢ with hcap
    · exact (hnextNot rfl).elim
    · rw [coolingRate, if_neg (not_le.mpr hsone)]
  have hx0 : 0 < s / (2 * t) := by positivity
  have hxhalf : s / (2 * t) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * t)]
    nlinarith
  have hlogLower : s / (4 * t) ≤ Real.log (1 + s / (2 * t)) := by
    have hraw := Real.le_log_one_add_of_nonneg hx0.le
    have hcompare : s / (4 * t) ≤
        2 * (s / (2 * t)) / (s / (2 * t) + 2) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 4 * t)
        (by positivity : 0 < s / (2 * t) + 2)]
      field_simp
      nlinarith
    exact hcompare.trans hraw
  have hnextOne : 1 < nextVariance q s :=
    hsone.trans_le (nextVariance_ge_self' q hs hst)
  have hpotential : scheduleLogPotential q (k + 1) -
      scheduleLogPotential q k = Real.log (1 + s / (2 * t)) := by
    rw [scheduleLogPotential, scheduleLogPotential, scheduleValue_succ]
    rw [max_eq_right hsone.le, max_eq_right hnextOne.le, hnext,
      Real.log_mul hs.ne' (by positivity)]
    ring
  rw [hpotential]
  calc
    s = 4 * t * (s / (4 * t)) := by field_simp
    _ ≤ 4 * t * Real.log (1 + s / (2 * t)) :=
      mul_le_mul_of_nonneg_left hlogLower (by positivity)

/-- Every nonterminal accelerated step pays for its current variance by an
increase of the clipped logarithmic potential. Slow steps cost only one. -/
theorem scheduleValue_charge_to_logPotential (q : VolumeParams) {k : ℕ}
    (hk : k + 1 < terminalPhaseSteps q) :
    max 1 (scheduleValue q k) ≤
      1 + 4 * terminalVariance q *
        (scheduleLogPotential q (k + 1) - scheduleLogPotential q k) := by
  let s := scheduleValue q k
  let t := terminalVariance q
  have hs : 0 < s := scheduleValue_pos q k
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (by
    simpa [t] using terminalVariance_ge_one' q)
  have hst : s ≤ t := scheduleValue_le_terminal q k
  have hpot : 0 ≤ scheduleLogPotential q (k + 1) -
      scheduleLogPotential q k := sub_nonneg.mpr <|
    scheduleLogPotential_mono q (Nat.le_add_right k 1)
  by_cases hsone : s ≤ 1
  · rw [max_eq_left hsone]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht.le) hpot]
  · have hsone' : 1 < s := lt_of_not_ge hsone
    have hnextNot : nextVariance q s ≠ t := by
      simpa [s, t, scheduleValue_succ] using
        scheduleValue_ne_terminal_of_lt_terminalPhaseSteps q hk
    have hnext : nextVariance q s = s * (1 + s / (2 * t)) := by
      unfold nextVariance at hnextNot ⊢
      rw [min_def] at hnextNot ⊢
      split_ifs at hnextNot ⊢ with hcap
      · exact (hnextNot rfl).elim
      · rw [coolingRate, if_neg (not_le.mpr hsone')]
    have hx0 : 0 < s / (2 * t) := by positivity
    have hxhalf : s / (2 * t) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * t)]
      nlinarith
    have hlogLower : s / (4 * t) ≤ Real.log (1 + s / (2 * t)) := by
      have hraw := Real.le_log_one_add_of_nonneg hx0.le
      have hcompare : s / (4 * t) ≤
          2 * (s / (2 * t)) / (s / (2 * t) + 2) := by
        rw [div_le_div_iff₀ (by positivity : 0 < 4 * t)
          (by positivity : 0 < s / (2 * t) + 2)]
        field_simp
        nlinarith
      exact hcompare.trans hraw
    have hnextPos : 0 < nextVariance q s := nextVariance_pos' q hs
    have hnextOne : 1 < nextVariance q s :=
      hsone'.trans_le (nextVariance_ge_self' q hs hst)
    have hpotential : scheduleLogPotential q (k + 1) -
        scheduleLogPotential q k = Real.log (1 + s / (2 * t)) := by
      rw [scheduleLogPotential, scheduleLogPotential, scheduleValue_succ]
      rw [max_eq_right hsone'.le, max_eq_right hnextOne.le, hnext,
        Real.log_mul hs.ne' (by positivity)]
      ring
    rw [max_eq_right hsone'.le, hpotential]
    have : s ≤ 4 * t * Real.log (1 + s / (2 * t)) := by
      calc
        s = 4 * t * (s / (4 * t)) := by field_simp
        _ ≤ 4 * t * Real.log (1 + s / (2 * t)) :=
          mul_le_mul_of_nonneg_left hlogLower (by positivity)
    linarith

theorem terminalPhaseSteps_pos (q : VolumeParams) : 0 < terminalPhaseSteps q := by
  by_contra h
  have hz : terminalPhaseSteps q = 0 := by omega
  have hterminal := scheduleValue_terminalPhaseSteps q
  rw [hz] at hterminal
  have hinitial : scheduleValue q 0 = initialVariance q := by
    simp [scheduleValue]
  rw [hinitial] at hterminal
  have : terminalVariance q < 1 := hterminal ▸ initialVariance_lt_one' q
  exact (not_lt_of_ge (terminalVariance_ge_one' q)) this

/-- The accelerated schedule has logarithmic amortized variance cost. This is
the deterministic heart of the cubic query accounting. -/
theorem sum_scheduleValue_max_le (q : VolumeParams) :
    (∑ k ∈ Finset.range (terminalPhaseSteps q),
        max 1 (scheduleValue q k)) ≤
      (terminalPhaseSteps q : ℝ) +
        4 * terminalVariance q * protectedLog (terminalVariance q) +
        terminalVariance q := by
  obtain ⟨last, hlast⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (terminalPhaseSteps_pos q))
  rw [hlast, Finset.sum_range_succ]
  have hprefix :
      (∑ k ∈ Finset.range last, max 1 (scheduleValue q k)) ≤
        (last : ℝ) + 4 * terminalVariance q *
          (scheduleLogPotential q last - scheduleLogPotential q 0) := by
    calc
      (∑ k ∈ Finset.range last, max 1 (scheduleValue q k)) ≤
          ∑ k ∈ Finset.range last,
            (1 + 4 * terminalVariance q *
              (scheduleLogPotential q (k + 1) - scheduleLogPotential q k)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply scheduleValue_charge_to_logPotential q
        have hk' := Finset.mem_range.mp hk
        omega
      _ = (last : ℝ) + 4 * terminalVariance q *
          (scheduleLogPotential q last - scheduleLogPotential q 0) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← Finset.mul_sum, Finset.sum_range_sub]
        ring
  have hpotential_zero : scheduleLogPotential q 0 = 0 := by
    rw [scheduleLogPotential]
    have hstart : scheduleValue q 0 = initialVariance q := by
      simp [scheduleValue]
    rw [hstart, max_eq_left (initialVariance_lt_one' q).le, Real.log_one]
  have hlast_le : max 1 (scheduleValue q last) ≤ terminalVariance q :=
    max_le (terminalVariance_ge_one' q) (scheduleValue_le_terminal q last)
  have hpotential_last : scheduleLogPotential q last ≤
      protectedLog (terminalVariance q) := by
    have hlog : Real.log (max 1 (scheduleValue q last)) ≤
        Real.log (terminalVariance q) := by
      exact Real.strictMonoOn_log.monotoneOn
        (lt_of_lt_of_le zero_lt_one
          (le_max_left (1 : ℝ) (scheduleValue q last)))
        (lt_of_lt_of_le zero_lt_one (terminalVariance_ge_one' q)) hlast_le
    exact hlog.trans (le_max_right _ _)
  have hprefix' :
      (∑ k ∈ Finset.range last, max 1 (scheduleValue q k)) ≤
        (last : ℝ) + 4 * terminalVariance q *
          protectedLog (terminalVariance q) := by
    rw [hpotential_zero, sub_zero] at hprefix
    exact hprefix.trans (by
      gcongr
      · exact mul_nonneg (by norm_num)
          (le_trans zero_le_one (terminalVariance_ge_one' q)))
  have hlastCost : max 1 (scheduleValue q last) ≤ terminalVariance q := hlast_le
  push_cast
  linarith

/-- The current variances of accelerated transitions have total logarithmic
charge.  This is the deterministic accumulation bound paired with the paper's
sharp accelerated moment estimate. -/
theorem sum_accelerated_scheduleValue_le (q : VolumeParams) :
    (∑ k ∈ Finset.range (terminalPhaseSteps q),
        if 1 < scheduleValue q k then scheduleValue q k else 0) ≤
      4 * terminalVariance q * protectedLog (terminalVariance q) +
        terminalVariance q := by
  classical
  obtain ⟨last, hlast⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (terminalPhaseSteps_pos q))
  rw [hlast, Finset.sum_range_succ]
  have hpot : ∀ k ∈ Finset.range last,
      (if 1 < scheduleValue q k then scheduleValue q k else 0) ≤
        4 * terminalVariance q *
          (scheduleLogPotential q (k + 1) - scheduleLogPotential q k) := by
    intro k hk
    split_ifs with hacc
    · apply scheduleValue_accelerated_charge_to_logPotential q
      · rw [hlast]
        have := Finset.mem_range.mp hk
        omega
      · exact hacc
    · have hmono := scheduleLogPotential_mono q
          (Nat.le_add_right k 1)
      have hT : 0 ≤ terminalVariance q :=
        (terminalVariance_ge_one' q).trans' zero_le_one
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hT)
        (sub_nonneg.mpr hmono)]
  have hprefix :
      (∑ k ∈ Finset.range last,
          if 1 < scheduleValue q k then scheduleValue q k else 0) ≤
        4 * terminalVariance q *
          (scheduleLogPotential q last - scheduleLogPotential q 0) := by
    calc
      _ ≤ ∑ k ∈ Finset.range last,
          4 * terminalVariance q *
            (scheduleLogPotential q (k + 1) - scheduleLogPotential q k) := by
        exact Finset.sum_le_sum fun k hk => hpot k hk
      _ = 4 * terminalVariance q *
          (scheduleLogPotential q last - scheduleLogPotential q 0) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub]
  have hpotential_zero : scheduleLogPotential q 0 = 0 := by
    rw [scheduleLogPotential]
    have hstart : scheduleValue q 0 = initialVariance q := by
      simp [scheduleValue]
    rw [hstart, max_eq_left (initialVariance_lt_one' q).le, Real.log_one]
  have hlast_le : scheduleValue q last ≤ terminalVariance q :=
    scheduleValue_le_terminal q last
  have hlast_term :
      (if 1 < scheduleValue q last then scheduleValue q last else 0) ≤
        terminalVariance q := by
    split_ifs
    · exact hlast_le
    · exact (terminalVariance_ge_one' q).trans' zero_le_one
  have hpotential_last : scheduleLogPotential q last ≤
      protectedLog (terminalVariance q) := by
    have hmax : max 1 (scheduleValue q last) ≤ terminalVariance q :=
      max_le (terminalVariance_ge_one' q) hlast_le
    have hlog : Real.log (max 1 (scheduleValue q last)) ≤
        Real.log (terminalVariance q) := by
      exact Real.strictMonoOn_log.monotoneOn
        (lt_of_lt_of_le zero_lt_one
          (le_max_left (1 : ℝ) (scheduleValue q last)))
        (lt_of_lt_of_le zero_lt_one (terminalVariance_ge_one' q)) hmax
    exact hlog.trans (le_max_right _ _)
  rw [hpotential_zero, sub_zero] at hprefix
  have hT : 0 ≤ terminalVariance q :=
    (terminalVariance_ge_one' q).trans' zero_le_one
  calc
    (∑ k ∈ Finset.range last,
        if 1 < scheduleValue q k then scheduleValue q k else 0) +
        (if 1 < scheduleValue q last then scheduleValue q last else 0) ≤
      4 * terminalVariance q * scheduleLogPotential q last +
        terminalVariance q := add_le_add hprefix hlast_term
    _ ≤ 4 * terminalVariance q * protectedLog (terminalVariance q) +
        terminalVariance q := by gcongr

noncomputable def explicitScheduleVariances (q : VolumeParams) : List ℝ :=
  List.ofFn fun i : Fin (terminalPhaseSteps q + 1) => scheduleValue q i

noncomputable def explicitVolumeCoolingSchedule (q : VolumeParams) :
    VolumeCoolingSchedule q where
  variances := explicitScheduleVariances q
  nonempty := by simp [explicitScheduleVariances]
  start := by simp [explicitScheduleVariances, scheduleValue]
  step := by
    rw [explicitScheduleVariances, List.isChain_ofFn]
    intro i hi
    exact scheduleValue_succ q i
  positive := by
    intro s hs
    rw [explicitScheduleVariances, List.mem_ofFn'] at hs
    obtain ⟨i, rfl⟩ := hs
    exact scheduleValue_pos q i
  finish := by
    rw [explicitScheduleVariances]
    have hne : (List.ofFn fun i : Fin (terminalPhaseSteps q + 1) =>
        scheduleValue q i) ≠ [] := by simp
    rw [List.getLast?_eq_some_getLast hne]
    congr 1
    rw [List.getLast_ofFn_succ]
    exact scheduleValue_terminalPhaseSteps q

theorem explicitSchedule_length_bound (q : VolumeParams) :
    (explicitVolumeCoolingSchedule q).variances.length ≤
      Nat.ceil
        (65536 * max 1 q.roundness * (q.n : ℝ) *
          protectedLog ((q.n : ℝ) / q.eps) *
          protectedLog (1 / q.eps) ^ 2) := by
  let n : ℝ := q.n
  let M : ℝ := max 1 q.roundness
  let Lₙ : ℝ := protectedLog (n / q.eps)
  let Lₑ : ℝ := protectedLog (1 / q.eps)
  let D : ℝ := M * n * Lₙ * Lₑ ^ 2
  let T : ℝ := terminalVariance q
  let N₁ : ℕ := slowPhaseSteps q
  let N₂ : ℕ := fastPhaseSteps q
  have hn : 3 ≤ n := by
    dsimp [n]
    exact_mod_cast q.dim_ok
  have hM : 1 ≤ M := le_max_left _ _
  have hLₙ : 1 ≤ Lₙ := le_max_left _ _
  have hLₑ : 1 ≤ Lₑ := le_max_left _ _
  have hLₑsq : 1 ≤ Lₑ ^ 2 := one_le_pow₀ hLₑ
  have hD : 3 ≤ D := by
    dsimp [D]
    have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
      intro a b ha hb
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
    have hrest : 1 ≤ M * Lₙ * Lₑ ^ 2 := hmul (hmul hM hLₙ) hLₑsq
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hrest)]
  have hL8 : protectedLog (8 / q.eps) ≤ 4 * Lₑ := by
    simpa [Lₑ] using protectedLog_eight_div_eps_le_four q
  have hT : T ≤ 16384 * M * n * Lₑ ^ 2 := by
    dsimp [T, terminalVariance]
    apply max_le
    · have : 1 ≤ 16384 * M * n * Lₑ ^ 2 := by
        have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
          intro a b ha hb
          nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
        have hbase := hmul (hmul hM (le_trans (by norm_num) hn)) hLₑsq
        nlinarith
      exact this
    · apply max_le
      · have hfactor : 1 ≤ 16384 * M * Lₑ ^ 2 := by
          have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
            intro a b ha hb
            nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
          have := hmul hM hLₑsq
          nlinarith
        nlinarith [mul_nonneg (le_trans (by norm_num) hn)
          (sub_nonneg.mpr hfactor)]
      · have hr : q.roundness ≤ M := le_max_right _ _
        have hn0 : 0 ≤ n := le_trans (by norm_num) hn
        have hLe0 : 0 ≤ Lₑ ^ 2 := sq_nonneg _
        have hround := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hr hn0) hLe0
        have hL8sq : protectedLog (8 / q.eps) ^ 2 ≤ 16 * Lₑ ^ 2 := by
          have hL80 : 0 ≤ protectedLog (8 / q.eps) :=
            le_trans zero_le_one (le_max_left _ _)
          have hsum0 : 0 ≤ 4 * Lₑ + protectedLog (8 / q.eps) := by positivity
          nlinarith [mul_nonneg (sub_nonneg.mpr hL8) hsum0]
        have hcoef : 0 ≤ 1024 * q.roundness * n :=
          mul_nonneg (mul_nonneg (by norm_num) q.roundness_pos.le) hn0
        have hscale := mul_le_mul_of_nonneg_left hL8sq
          hcoef
        have hroundScaled := mul_le_mul_of_nonneg_left hround
          (by norm_num : (0 : ℝ) ≤ 16384)
        nlinarith [hscale, hroundScaled]
  have hslow_nonneg : 0 ≤ 2 * n * (6 + Lₙ) := by positivity
  have hN₁ : (N₁ : ℝ) < 2 * n * (6 + Lₙ) + 1 := by
    simpa [N₁, slowPhaseSteps, n, Lₙ] using Nat.ceil_lt_add_one hslow_nonneg
  have hN₂ : (N₂ : ℝ) < 3 * T + 1 := by
    have : 0 ≤ 3 * T := by
      exact mul_nonneg (by norm_num) (le_trans zero_le_one (by
        simpa [T] using terminalVariance_ge_one' q))
    simpa [N₂, fastPhaseSteps, T] using Nat.ceil_lt_add_one this
  have hslowD : 2 * n * (6 + Lₙ) ≤ 14 * D := by
    have h6 : 6 + Lₙ ≤ 7 * Lₙ := by linarith
    have hn0 : 0 ≤ n := le_trans (by norm_num) hn
    have hfirst : 2 * n * (6 + Lₙ) ≤ 14 * n * Lₙ := by nlinarith
    have hfactor : n * Lₙ ≤ D := by
      dsimp [D]
      have hnl : 0 ≤ n * Lₙ := mul_nonneg hn0 (le_trans zero_le_one hLₙ)
      have hfac : 1 ≤ M * Lₑ ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sub_nonneg.mpr hLₑsq)]
      nlinarith [mul_nonneg hnl (sub_nonneg.mpr hfac)]
    linarith
  have hfastD : 3 * T ≤ 49152 * D := by
    have hLn0 : 0 ≤ Lₙ := le_trans zero_le_one hLₙ
    have hbase0 : 0 ≤ M * n * Lₑ ^ 2 := by positivity
    have : M * n * Lₑ ^ 2 ≤ D := by
      dsimp [D]
      nlinarith [mul_nonneg hbase0 (sub_nonneg.mpr hLₙ)]
    nlinarith
  have hcast : ((N₁ + N₂ + 1 : ℕ) : ℝ) ≤ 65536 * D := by
    push_cast
    linarith
  have hnat : N₁ + N₂ + 1 ≤ Nat.ceil (65536 * D) := by
    exact_mod_cast le_trans hcast (Nat.le_ceil (65536 * D))
  have hstop : terminalPhaseSteps q + 1 ≤ N₁ + N₂ + 1 := by
    have := Nat.add_le_add_right (terminalPhaseSteps_le_total q) 1
    simpa [totalPhaseSteps, N₁, N₂, Nat.add_assoc] using this
  have hfinal := le_trans hstop hnat
  simpa [explicitVolumeCoolingSchedule, explicitScheduleVariances, totalPhaseSteps,
    N₁, N₂, D, M, n, Lₙ, Lₑ, mul_assoc] using hfinal

theorem volume_proof_schedule :
    ∃ S : (q : VolumeParams) → VolumeCoolingSchedule q,
      ∀ q : VolumeParams,
        (S q).variances.length ≤
          Nat.ceil
            (65536 * max 1 q.roundness * (q.n : ℝ) *
              protectedLog ((q.n : ℝ) / q.eps) *
              protectedLog (1 / q.eps) ^ 2) := by
  exact ⟨explicitVolumeCoolingSchedule, explicitSchedule_length_bound⟩

end ArlibCommunity.Algorithms.CV18
