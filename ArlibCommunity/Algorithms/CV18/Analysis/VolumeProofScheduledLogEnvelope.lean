/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduleTargetedKLS
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofRetryTailBudget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofDependentSchedule
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSchedule

/-!
# The scheduled CV18 logarithmic factors are polylogarithmic

The scheduled, amplified CV18 query rate carries six logarithmic factors
(`figureOneScheduledLogEnvelope`): of `1/p`, `1/ε`, `n/ε`, the terminal variance, the
schedule's accuracy, and the block mixing error. Each is the logarithm of a quantity that
is polynomial in `n`, `1/ε`, `1/p` and the roundness, so each is at most a constant times

  `Λ = volumeParamLog q = protectedLog (n · max(1, roundness) / (ε · p))`.

`figureOneScheduledLogEnvelope_le` makes this explicit:
`figureOneScheduledLogEnvelope q ≤ 14113440000 · Λ¹⁰`.

The only non-closed-form ingredient, the phase count `terminalPhaseSteps q + 1`, is
bounded through `terminalPhaseSteps_le_total`.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- The CV18 input size `n · max(1, roundness) / (ε · p)`. -/
noncomputable def volumeParamSize (q : VolumeParams) : ℝ :=
  (q.n : ℝ) * max 1 q.roundness / (q.eps * q.p)

/-- `log` of the CV18 input size, protected below by `1`. -/
noncomputable def volumeParamLog (q : VolumeParams) : ℝ :=
  protectedLog (volumeParamSize q)

/-- The six logarithmic factors in the scheduled, amplified CV18 query rate. -/
noncomputable def figureOneScheduledLogEnvelope (q : VolumeParams) : ℝ :=
  protectedLog (1 / q.p) *
  protectedLog (1 / q.eps) ^ 2 *
  protectedLog ((q.n : ℝ) / q.eps) ^ 2 *
  protectedLog (terminalScale q) ^ 2 *
  accuracyLog q *
  protectedLog (1 / blockMixingError q
    (maxRetries q - 1)) ^ 2

theorem one_le_protectedLog (x : ℝ) : 1 ≤ protectedLog x := le_max_left _ _

/-- `protectedLog x ≤ x` for `x ≥ 1`. -/
theorem protectedLog_le_self {x : ℝ} (hx : 1 ≤ x) : protectedLog x ≤ x := by
  apply max_le hx
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x)
  linarith

/-- The basic estimate: the logarithm of a quantity bounded by `2ᵃ Xᵏ` is at most
`(a + k) · protectedLog X`. -/
theorem protectedLog_le_of_le_two_pow_mul_pow {X y : ℝ} (a k : ℕ) (hk : 1 ≤ k)
    (hX : 1 ≤ X) (hy0 : 0 < y) (hy : y ≤ 2 ^ a * X ^ k) :
    protectedLog y ≤ (a + k) * protectedLog X := by
  have hL := one_le_protectedLog X
  have hlogX : Real.log X ≤ protectedLog X := le_max_right _ _
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogy : Real.log y ≤ a * Real.log 2 + k * Real.log X := by
    calc Real.log y ≤ Real.log (2 ^ a * X ^ k) := Real.log_le_log hy0 hy
      _ = a * Real.log 2 + k * Real.log X := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  apply max_le
  · nlinarith
  · have h1 : (a : ℝ) * Real.log 2 ≤ a * protectedLog X := by
      have : Real.log 2 ≤ protectedLog X := by linarith
      exact mul_le_mul_of_nonneg_left this ha
    have h2 : (k : ℝ) * Real.log X ≤ k * protectedLog X :=
      mul_le_mul_of_nonneg_left hlogX (by linarith)
    nlinarith

section Bounds

variable (q : VolumeParams)

/-- The basic inequalities between the CV18 input size and its parts. -/
theorem volumeParam_size_facts :
    let X := volumeParamSize q
    1 ≤ X ∧ (q.n : ℝ) ≤ X ∧ 1 / q.eps ≤ X ∧ 1 / q.p ≤ X ∧ (q.n : ℝ) / q.eps ≤ X ∧
      (q.n : ℝ) * max 1 q.roundness / q.eps ≤ X := by
  intro X
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have he0 := q.heps.1
  have he1 := q.heps.2
  have hp0 := q.hp.1
  have hp1 := q.hp.2
  have hM : (1 : ℝ) ≤ max 1 q.roundness := le_max_left _ _
  have hnM : (1 : ℝ) ≤ (q.n : ℝ) * max 1 q.roundness := by nlinarith
  have hep : 0 < q.eps * q.p := mul_pos he0 hp0
  have hX : X = (q.n : ℝ) * max 1 q.roundness / (q.eps * q.p) := rfl
  have hnMeps : (q.n : ℝ) * max 1 q.roundness / q.eps ≤ X := by
    rw [hX, div_le_div_iff₀ he0 hep]
    have : 0 ≤ (q.n : ℝ) * max 1 q.roundness := by linarith
    nlinarith [mul_nonneg this he0.le]
  have hneps : (q.n : ℝ) / q.eps ≤ X := by
    refine le_trans ?_ hnMeps
    apply div_le_div_of_nonneg_right _ he0.le
    nlinarith
  have heps : 1 / q.eps ≤ X := by
    refine le_trans ?_ hneps
    apply div_le_div_of_nonneg_right _ he0.le
    linarith
  have hpX : 1 / q.p ≤ X := by
    rw [hX, div_le_div_iff₀ hp0 hep]
    nlinarith [mul_pos he0 hp0]
  have hnX : (q.n : ℝ) ≤ X := by
    refine le_trans ?_ hneps
    rw [le_div_iff₀ he0]
    nlinarith
  have h1 : (1 : ℝ) ≤ X := le_trans (by linarith) hnX
  exact ⟨h1, hnX, heps, hpX, hneps, hnMeps⟩

/-- The terminal variance is at most `2¹⁶ X²`. -/
theorem terminalScale_le :
    terminalScale q ≤ 2 ^ 16 * volumeParamSize q ^ 2 := by
  obtain ⟨h1, hnX, heX, -, -, hnMeX⟩ := volumeParam_size_facts q
  set X := volumeParamSize q
  have he0 := q.heps.1
  have he1 := q.heps.2
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hM : q.roundness ≤ max 1 q.roundness := le_max_right _ _
  have hρ := q.roundness_pos
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hnM2 : (q.n : ℝ) * max 1 q.roundness / q.eps ^ 2 ≤ X ^ 2 := by
    have := mul_le_mul hnMeX heX (by positivity) (by linarith)
    calc (q.n : ℝ) * max 1 q.roundness / q.eps ^ 2
        = (q.n : ℝ) * max 1 q.roundness / q.eps * (1 / q.eps) := by
          field_simp
      _ ≤ X * X := this
      _ = X ^ 2 := by ring
  have h8 : protectedLog (8 / q.eps) ≤ 8 / q.eps := protectedLog_le_self (by
    rw [le_div_iff₀ he0]; linarith)
  have hpl0 : 0 ≤ protectedLog (8 / q.eps) := by
    linarith [one_le_protectedLog (8 / q.eps)]
  have hthird : 1024 * q.roundness * (q.n : ℝ) * protectedLog (8 / q.eps) ^ 2 ≤
      2 ^ 16 * X ^ 2 := by
    have hsq : protectedLog (8 / q.eps) ^ 2 ≤ (8 / q.eps) ^ 2 :=
      pow_le_pow_left₀ hpl0 h8 2
    calc 1024 * q.roundness * (q.n : ℝ) * protectedLog (8 / q.eps) ^ 2
        ≤ 1024 * max 1 q.roundness * (q.n : ℝ) * (8 / q.eps) ^ 2 := by
          gcongr
      _ = 2 ^ 16 * ((q.n : ℝ) * max 1 q.roundness / q.eps ^ 2) := by
          field_simp
          ring
      _ ≤ 2 ^ 16 * X ^ 2 := by gcongr
  unfold terminalScale
  apply max_le
  · nlinarith
  · apply max_le
    · nlinarith
    · exact hthird

/-- The phase count is at most `2¹⁸ X²`. -/
theorem numPhases_le :
    (numPhases q : ℝ) ≤ 2 ^ 18 * volumeParamSize q ^ 2 := by
  obtain ⟨h1, hnX, heX, -, hneX, -⟩ := volumeParam_size_facts q
  set X := volumeParamSize q
  have he0 := q.heps.1
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hT := terminalScale_le q
  have hT1 : (1 : ℝ) ≤ terminalScale q := le_max_left _ _
  have hsteps : (terminalPhaseSteps q : ℝ) ≤ slowPhaseSteps q + fastPhaseSteps q := by
    have := terminalPhaseSteps_le_total q
    unfold totalPhaseSteps at this
    exact_mod_cast this
  have hslow := slowPhaseSteps_cast_le q
  have hL : protectedLog ((q.n : ℝ) / q.eps) ≤ (q.n : ℝ) / q.eps :=
    protectedLog_le_self (by rw [le_div_iff₀ he0]; linarith [q.heps.2])
  have hnn : (q.n : ℝ) * ((q.n : ℝ) / q.eps) ≤ X ^ 2 := by
    have := mul_le_mul hnX hneX (by positivity) (by linarith)
    nlinarith
  have hfast : (fastPhaseSteps q : ℝ) ≤ 3 * terminalScale q + 1 := by
    unfold fastPhaseSteps terminalVariance
    exact (Nat.ceil_lt_add_one (by linarith)).le
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hslow' : (slowPhaseSteps q : ℝ) ≤ 15 * X ^ 2 := by
    have : 15 * (q.n : ℝ) * protectedLog ((q.n : ℝ) / q.eps) ≤
        15 * ((q.n : ℝ) * ((q.n : ℝ) / q.eps)) := by
      have := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 15 * q.n)
      linarith
    linarith
  unfold numPhases
  push_cast
  nlinarith

/-- The largest per-phase sample count is at most `2²⁶ X⁴`. -/
theorem largestSampleCount_le :
    (largestSampleCount q : ℝ) ≤ 2 ^ 26 * volumeParamSize q ^ 4 := by
  obtain ⟨h1, hnX, heX, -, hneX, -⟩ := volumeParam_size_facts q
  set X := volumeParamSize q
  have he0 := q.heps.1
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hT := terminalScale_le q
  have hT1 : (1 : ℝ) ≤ terminalScale q := le_max_left _ _
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hX3 : X ≤ X ^ 2 := by nlinarith
  have hX4 : 1 ≤ X ^ 4 := by nlinarith
  have he2 : 1 / q.eps ^ 2 ≤ X ^ 2 := by
    have := mul_le_mul heX heX (by positivity) (by linarith)
    calc 1 / q.eps ^ 2 = 1 / q.eps * (1 / q.eps) := by field_simp
      _ ≤ X * X := this
      _ = X ^ 2 := by ring
  have hL : protectedLog ((q.n : ℝ) / q.eps) ≤ (q.n : ℝ) / q.eps :=
    protectedLog_le_self (by rw [le_div_iff₀ he0]; linarith [q.heps.2])
  have hfixed : (fixedRateSampleCount q : ℝ) ≤ 2 ^ 26 * X ^ 4 := by
    unfold fixedRateSampleCount
    have hc := (Nat.ceil_lt_add_one (by
      have := one_le_protectedLog ((q.n : ℝ) / q.eps)
      positivity : (0 : ℝ) ≤ 4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2)).le
    have hb : 4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2 ≤ 4096 * (X * X ^ 2) := by
      calc 4096 * protectedLog ((q.n : ℝ) / q.eps) / q.eps ^ 2
          = 4096 * protectedLog ((q.n : ℝ) / q.eps) * (1 / q.eps ^ 2) := by ring
        _ ≤ 4096 * X * X ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hL.trans hneX) (by norm_num)) he2
            (by positivity) (by positivity)
        _ = 4096 * (X * X ^ 2) := by ring
    nlinarith
  have hsample : (sampleCount q : ℝ) ≤ 2 ^ 26 * X ^ 4 := by
    unfold sampleCount
    have hpl : protectedLog (terminalVariance q) ≤ terminalScale q :=
      protectedLog_le_self hT1
    have hc := (Nat.ceil_lt_add_one (by
      have := one_le_protectedLog (terminalVariance q)
      positivity : (0 : ℝ) ≤ 512 * protectedLog (terminalVariance q) / q.eps ^ 2)).le
    have hb : 512 * protectedLog (terminalVariance q) / q.eps ^ 2 ≤ 2 ^ 25 * X ^ 4 := by
      calc 512 * protectedLog (terminalVariance q) / q.eps ^ 2
          = 512 * protectedLog (terminalVariance q) * (1 / q.eps ^ 2) := by ring
        _ ≤ 512 * (2 ^ 16 * X ^ 2) * X ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hpl.trans hT) (by norm_num)) he2
            (by positivity) (by positivity)
        _ = 2 ^ 25 * X ^ 4 := by ring
    nlinarith
  unfold largestSampleCount
  push_cast
  exact max_le hfixed hsample

/-- The inverse per-sample mixing error, written out. -/
theorem one_div_figureOnePerSampleMixingError_eq :
    1 / sampleMixingError q =
      3 * 4096 * 1024 ^ 4 * (largestSampleCount q : ℝ) *
        (numPhases q : ℝ) ^ 6 / q.eps ^ 10 := by
  have he0 := q.heps.1
  have hk : (0 : ℝ) < largestSampleCount q := by
    exact_mod_cast largestSampleCount_pos q
  have hm : (0 : ℝ) < numPhases q := by
    exact_mod_cast numPhases_pos q
  unfold sampleMixingError dependenceError truncationLevel
  field_simp

/-- The inverse per-sample mixing error is at most `2¹⁸⁸ X²⁶`. -/
theorem one_div_figureOnePerSampleMixingError_le :
    1 / sampleMixingError q ≤ 2 ^ 188 * volumeParamSize q ^ 26 := by
  obtain ⟨h1, -, heX, -, -, -⟩ := volumeParam_size_facts q
  set X := volumeParamSize q
  have he0 := q.heps.1
  have hS := largestSampleCount_le q
  have hΦ := numPhases_le q
  have hS0 : (0 : ℝ) ≤ largestSampleCount q := Nat.cast_nonneg _
  have hΦ0 : (0 : ℝ) ≤ numPhases q := Nat.cast_nonneg _
  rw [one_div_figureOnePerSampleMixingError_eq]
  calc 3 * 4096 * 1024 ^ 4 * (largestSampleCount q : ℝ) *
        (numPhases q : ℝ) ^ 6 / q.eps ^ 10
      = 3 * 4096 * 1024 ^ 4 * (largestSampleCount q : ℝ) *
        (numPhases q : ℝ) ^ 6 * (1 / q.eps) ^ 10 := by
        field_simp
    _ ≤ 2 ^ 54 * (2 ^ 26 * X ^ 4) * (2 ^ 18 * X ^ 2) ^ 6 * X ^ 10 := by
        gcongr
        norm_num
    _ = 2 ^ 188 * X ^ 26 := by ring

/-- The inverse per-sample mixing error is at least `1`. -/
theorem one_le_one_div_figureOnePerSampleMixingError :
    1 ≤ 1 / sampleMixingError q := by
  have he0 := q.heps.1
  have he1 := q.heps.2
  have hk : (1 : ℝ) ≤ largestSampleCount q := by
    exact_mod_cast largestSampleCount_pos q
  have hm : (1 : ℝ) ≤ numPhases q := by
    exact_mod_cast numPhases_pos q
  have he10 : q.eps ^ 10 ≤ 1 := pow_le_one₀ he0.le he1.le
  have he10pos : 0 < q.eps ^ 10 := by positivity
  rw [one_div_figureOnePerSampleMixingError_eq, le_div_iff₀ he10pos]
  have hm6 : (1 : ℝ) ≤ (numPhases q : ℝ) ^ 6 := one_le_pow₀ hm
  nlinarith [mul_le_mul hk hm6 zero_le_one (by linarith)]

/-- The schedule's accuracy logarithm is at most `225 Λ`. -/
theorem accuracyLog_le :
    accuracyLog q ≤ 225 * volumeParamLog q := by
  obtain ⟨h1, hnX, -, -, -, -⟩ := volumeParam_size_facts q
  set X := volumeParamSize q
  have hP0 := sampleMixingError_pos q
  have hinv := one_div_figureOnePerSampleMixingError_le q
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hbound : ∀ c : ℝ, 0 < c → c ≤ 1024 →
      protectedLog ((q.n : ℝ) / (sampleMixingError q / c)) ≤
        225 * volumeParamLog q := by
    intro c hc0 hc
    have hy : (q.n : ℝ) / (sampleMixingError q / c) ≤ 2 ^ 198 * X ^ 27 := by
      calc (q.n : ℝ) / (sampleMixingError q / c)
          = c * (q.n : ℝ) * (1 / sampleMixingError q) := by
            field_simp
        _ ≤ 1024 * X * (2 ^ 188 * X ^ 26) := by
            apply mul_le_mul (mul_le_mul hc hnX (by positivity) (by norm_num)) hinv
              (by positivity) (by positivity)
        _ = 2 ^ 198 * X ^ 27 := by ring
    have := protectedLog_le_of_le_two_pow_mul_pow 198 27 (by norm_num) h1
      (by positivity) hy
    unfold volumeParamLog
    norm_num at this ⊢
    exact this
  unfold accuracyLog coreMixingError
    radialError
  exact max_le (hbound 768 (by norm_num) (by norm_num))
    (hbound 8 (by norm_num) (by norm_num))

set_option exponentiation.threshold 400 in
/-- The inverse block mixing error at the safe retry count is at most `2³⁸⁸ X⁵²`. -/
theorem one_div_figureOneCorrectedBlockMixingError_le :
    1 / blockMixingError q (maxRetries q - 1) ≤
      2 ^ 388 * volumeParamSize q ^ 52 := by
  obtain ⟨h1, -, -, -, -, -⟩ := volumeParam_size_facts q
  set X := volumeParamSize q
  set P := sampleMixingError q with hPdef
  have hP0 : 0 < P := sampleMixingError_pos q
  have hinv : 1 / P ≤ 2 ^ 188 * X ^ 26 := one_div_figureOnePerSampleMixingError_le q
  have hinv1 : 1 ≤ 1 / P := one_le_one_div_figureOnePerSampleMixingError q
  have hR1 : 1 ≤ maxRetries q := maxRetries_pos q
  have hRcast : ((maxRetries q - 1 : ℕ) : ℝ) + 1 = maxRetries q := by
    have h := Nat.sub_add_cancel hR1
    exact_mod_cast h
  have h4P : 1 ≤ 4 / P := by
    have : 4 / P = 4 * (1 / P) := by ring
    rw [this]; linarith
  have hR : (maxRetries q : ℝ) ≤ 513 * (1 / P) := by
    have h4 : 4 / P = 4 * (1 / P) := by ring
    have hpl : protectedLog (4 / P) ≤ 4 * (1 / P) := h4 ▸ protectedLog_le_self h4P
    have hc : (maxRetries q : ℝ) ≤ 128 * protectedLog (4 / P) + 1 := by
      unfold maxRetries
      rw [← hPdef]
      exact (Nat.ceil_lt_add_one (by
        have := one_le_protectedLog (4 / P)
        positivity : (0 : ℝ) ≤ 128 * protectedLog (4 / P))).le
    linarith
  have heq : 1 / blockMixingError q (maxRetries q - 1) =
      4 * (maxRetries q : ℝ) * (1 / P) := by
    unfold blockMixingError
    rw [hRcast, ← hPdef]
    field_simp
  rw [heq]
  have hX26 : 0 ≤ 2 ^ 188 * X ^ 26 := by positivity
  calc 4 * (maxRetries q : ℝ) * (1 / P)
      ≤ 4 * (513 * (1 / P)) * (1 / P) := by
        gcongr
    _ ≤ 4 * (513 * (2 ^ 188 * X ^ 26)) * (2 ^ 188 * X ^ 26) := by
        gcongr
    _ = (2052 * 2 ^ 376) * X ^ 52 := by ring
    _ ≤ 2 ^ 388 * X ^ 52 := by
        gcongr
        norm_num

/-- **The scheduled CV18 logarithmic factors are polylogarithmic.**
`figureOneScheduledLogEnvelope q ≤ 14113440000 · Λ¹⁰` with
`Λ = protectedLog (n · max(1, roundness) / (ε · p))`. -/
theorem figureOneScheduledLogEnvelope_le :
    figureOneScheduledLogEnvelope q ≤ 14113440000 * volumeParamLog q ^ 10 := by
  obtain ⟨h1, hnX, heX, hpX, hneX, -⟩ := volumeParam_size_facts q
  set X := volumeParamSize q
  set Λ := volumeParamLog q with hΛ
  have hΛ1 : 1 ≤ Λ := one_le_protectedLog _
  have he0 := q.heps.1
  have hp0 := q.hp.1
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have one_step : ∀ y : ℝ, 0 < y → y ≤ X → protectedLog y ≤ Λ := by
    intro y hy0 hy
    have := protectedLog_le_of_le_two_pow_mul_pow 0 1 le_rfl h1 hy0 (by simpa using hy)
    simpa [hΛ, volumeParamLog] using this
  have f1 : protectedLog (1 / q.p) ≤ Λ := one_step _ (by positivity) hpX
  have f2 : protectedLog (1 / q.eps) ≤ Λ := one_step _ (by positivity) heX
  have f3 : protectedLog ((q.n : ℝ) / q.eps) ≤ Λ := one_step _ (by positivity) hneX
  have f4 : protectedLog (terminalScale q) ≤ 18 * Λ := by
    have hT1 : (1 : ℝ) ≤ terminalScale q := le_max_left _ _
    have := protectedLog_le_of_le_two_pow_mul_pow 16 2 (by norm_num) h1 (by linarith)
      (terminalScale_le q)
    norm_num at this
    simpa [hΛ, volumeParamLog] using this
  have f5 : accuracyLog q ≤ 225 * Λ := accuracyLog_le q
  have f6 : protectedLog (1 / blockMixingError q
      (maxRetries q - 1)) ≤ 440 * Λ := by
    have hpos : 0 < 1 / blockMixingError q
        (maxRetries q - 1) := by
      have hP0 := sampleMixingError_pos q
      unfold blockMixingError
      positivity
    have := protectedLog_le_of_le_two_pow_mul_pow 388 52 (by norm_num) h1 hpos
      (one_div_figureOneCorrectedBlockMixingError_le q)
    norm_num at this
    simpa [hΛ, volumeParamLog] using this
  have n1 := one_le_protectedLog (1 / q.p)
  have n2 := one_le_protectedLog (1 / q.eps)
  have n3 := one_le_protectedLog ((q.n : ℝ) / q.eps)
  have n4 := one_le_protectedLog (terminalScale q)
  have n5 : 1 ≤ accuracyLog q := accuracyLog_one_le q
  have n6 := one_le_protectedLog (1 / blockMixingError q
      (maxRetries q - 1))
  unfold figureOneScheduledLogEnvelope
  calc protectedLog (1 / q.p) * protectedLog (1 / q.eps) ^ 2 *
        protectedLog ((q.n : ℝ) / q.eps) ^ 2 * protectedLog (terminalScale q) ^ 2 *
        accuracyLog q *
        protectedLog (1 / blockMixingError q
          (maxRetries q - 1)) ^ 2
      ≤ Λ * Λ ^ 2 * Λ ^ 2 * (18 * Λ) ^ 2 * (225 * Λ) * (440 * Λ) ^ 2 := by
        gcongr
    _ = 14113440000 * Λ ^ 10 := by ring

end Bounds

end ArlibCommunity.Algorithms.CV18
