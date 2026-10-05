/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofThirdMomentLogConcavity
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependentThirdMoment
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGaussianDeathArithmetic

/-!
# Concrete third moments for the fixed CV18 cooling schedule

The fourth moment becomes singular at the dimension-three fixed update
`t / s = 4 / 3`.  The third moment stays finite.  This module specializes the
one-third partition inequality to that endpoint and records a rational `L³`
constant suitable for the approximate-covariance theorem.
-/

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-- On a dimension-three fixed-rate update, the precision-ratio base in the
one-third partition inequality is at most `27 / 16`. -/
theorem fixedRate_thirdMoment_precisionFactor_le
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hstep : t ≤ s * (1 + 1 / (3 : ℝ))) :
    s ^ 3 / (t ^ 2 * (3 * s - 2 * t)) ≤ 27 / 16 := by
  have ht : 0 < t := hs.trans_le hst
  have hthree : 0 < 3 * s - 2 * t := by nlinarith
  have hfirst : 0 ≤ 4 * s - 3 * t := by nlinarith
  have hsecond : 0 ≤ 18 * t ^ 2 - 3 * s * t - 4 * s ^ 2 := by
    have hprod : 0 ≤ (t - s) * (18 * t + 15 * s) :=
      mul_nonneg (sub_nonneg.mpr hst) (by positivity)
    nlinarith [sq_pos_of_pos hs]
  have hfactor :
      27 * t ^ 2 * (3 * s - 2 * t) - 16 * s ^ 3 =
        (4 * s - 3 * t) * (18 * t ^ 2 - 3 * s * t - 4 * s ^ 2) := by
    ring
  rw [div_le_iff₀ (mul_pos (sq_pos_of_pos ht) hthree)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
  have hnonneg := mul_nonneg hfirst hsecond
  rw [← hfactor] at hnonneg
  nlinarith

/-- Dimension-dependent sharp endpoint bound for the precision factor of a
fixed-rate cooling step. -/
theorem fixedRate_thirdMoment_precisionFactor_le_dimension
    {n s t : ℝ} (hn : 3 ≤ n) (hs : 0 < s) (hst : s ≤ t)
    (hstep : t ≤ s * (1 + 1 / n)) :
    s ^ 3 / (t ^ 2 * (3 * s - 2 * t)) ≤
      n ^ 3 / ((n + 1) ^ 2 * (n - 2)) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have ht : 0 < t := hs.trans_le hst
  have hstepThree : t ≤ s * (4 / 3 : ℝ) := by
    have hinv : 1 / n ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) hn
    calc
      t ≤ s * (1 + 1 / n) := hstep
      _ ≤ s * (4 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hs.le
        linarith
  have hthree : 0 < 3 * s - 2 * t := by nlinarith
  have hcap : 0 ≤ (n + 1) * s - n * t := by
    have hmul := mul_le_mul_of_nonneg_left hstep hnpos.le
    field_simp [hnpos.ne'] at hmul
    nlinarith
  have htSub : 0 ≤ t - s := sub_nonneg.mpr hst
  have hinner :
      0 ≤ 2 * n ^ 2 * t ^ 2 - n * (n - 2) * s * t -
        (n + 1) * (n - 2) * s ^ 2 := by
    have hfirst : 0 ≤ 2 * n ^ 2 * t * (t - s) := by positivity
    have hsecond : 0 ≤ n * (n + 2) * s * (t - s) := by positivity
    have hthird : 0 ≤ (3 * n + 2) * s ^ 2 := by positivity
    nlinarith
  have hfactor :
      n ^ 3 * (t ^ 2 * (3 * s - 2 * t)) -
          (n + 1) ^ 2 * (n - 2) * s ^ 3 =
        ((n + 1) * s - n * t) *
          (2 * n ^ 2 * t ^ 2 - n * (n - 2) * s * t -
            (n + 1) * (n - 2) * s ^ 2) := by
    ring
  have hnonneg :
      0 ≤ n ^ 3 * (t ^ 2 * (3 * s - 2 * t)) -
          (n + 1) ^ 2 * (n - 2) * s ^ 3 := by
    rw [hfactor]
    positivity
  rw [div_le_div_iff₀
    (mul_pos (sq_pos_of_pos ht) hthree)
    (mul_pos (sq_pos_of_pos (by linarith : 0 < n + 1)) (by linarith))]
  nlinarith

/-- The dimension-dependent endpoint factor, raised to its Gaussian
partition exponent, is uniformly worst in dimension three. -/
theorem fixedRate_thirdMoment_dimensionFactor_pow_le
    (n : ℕ) (hn : 3 ≤ n) :
    (((n : ℝ) ^ 3 /
        (((n : ℝ) + 1) ^ 2 * ((n : ℝ) - 2))) ^ (n + 1)) ≤
      (27 / 16 : ℝ) ^ 4 := by
  rcases eq_or_lt_of_le hn with rfl | hn3
  · norm_num
  rcases eq_or_lt_of_le (Nat.succ_le_iff.mpr hn3) with rfl | hn4
  · norm_num
  have hn5 : 5 ≤ n := Nat.succ_le_iff.mpr hn4
  let N : ℝ := n
  have hN5 : (5 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hn5
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN5
  have hNp1 : 0 < N + 1 := by linarith
  have hNm2 : 0 < N - 2 := by linarith
  have hdenPos : 0 < (N + 1) ^ 2 * (N - 2) :=
    mul_pos (sq_pos_of_pos hNp1) hNm2
  have hbaseEq :
      N ^ 3 / ((N + 1) ^ 2 * (N - 2)) =
        1 + (3 * N + 2) / ((N + 1) ^ 2 * (N - 2)) := by
    rw [div_eq_iff hdenPos.ne']
    field_simp [hdenPos.ne']
    ring
  have hpoly :
      N ^ 2 * (3 * N + 2) ≤ 5 * ((N + 1) ^ 2 * (N - 2)) := by
    have hNminus : 0 ≤ N - 5 := by linarith
    have hsq : 0 ≤ N ^ 2 := sq_nonneg N
    have hcubic : 5 * N ^ 2 ≤ N ^ 3 := by
      have := mul_nonneg hsq hNminus
      nlinarith
    have hsquareLinear : 5 * N ≤ N ^ 2 := by
      have := mul_nonneg hNpos.le hNminus
      nlinarith
    nlinarith
  have hfrac :
      (3 * N + 2) / ((N + 1) ^ 2 * (N - 2)) ≤ 5 / N ^ 2 := by
    rw [div_le_div_iff₀ hdenPos (sq_pos_of_pos hNpos)]
    nlinarith [hpoly]
  have hbase :
      N ^ 3 / ((N + 1) ^ 2 * (N - 2)) ≤ 1 + 5 / N ^ 2 := by
    rw [hbaseEq]
    linarith
  have hbase0 : 0 ≤ N ^ 3 / ((N + 1) ^ 2 * (N - 2)) := by positivity
  have hone0 : 0 ≤ 1 + 5 / N ^ 2 := by positivity
  have hpow :
      (N ^ 3 / ((N + 1) ^ 2 * (N - 2))) ^ (n + 1) ≤
        (1 + 5 / N ^ 2) ^ (n + 1) :=
    pow_le_pow_left₀ hbase0 hbase (n + 1)
  have honeExp : 1 + 5 / N ^ 2 ≤ Real.exp (5 / N ^ 2) := by
    simpa [add_comm] using Real.add_one_le_exp (5 / N ^ 2)
  have hpowExp :
      (1 + 5 / N ^ 2) ^ (n + 1) ≤
        Real.exp (((n + 1 : ℕ) : ℝ) * (5 / N ^ 2)) := by
    have hp := pow_le_pow_left₀ hone0 honeExp (n + 1)
    rw [← Real.exp_nat_mul] at hp
    simpa [mul_comm] using hp
  have hexponent : ((n + 1 : ℕ) : ℝ) * (5 / N ^ 2) ≤ 6 / 5 := by
    have hNcast : ((n + 1 : ℕ) : ℝ) = N + 1 := by
      simp [N]
    rw [hNcast]
    calc
      (N + 1) * (5 / N ^ 2) = 5 * (N + 1) / N ^ 2 := by ring
      _ ≤ 6 / 5 := by
        rw [div_le_iff₀ (sq_pos_of_pos hNpos)]
        nlinarith [sq_nonneg (N - 5)]
  have hexpFour : Real.exp (6 / 5 : ℝ) ≤ 4 := by
    convert Real.exp_le_two_add_div_two_sub (x := (6 / 5 : ℝ))
      (by norm_num) (by norm_num) using 1 <;> norm_num
  calc
    (N ^ 3 / ((N + 1) ^ 2 * (N - 2))) ^ (n + 1) ≤
        (1 + 5 / N ^ 2) ^ (n + 1) := hpow
    _ ≤ Real.exp (((n + 1 : ℕ) : ℝ) * (5 / N ^ 2)) := hpowExp
    _ ≤ Real.exp (6 / 5) := Real.exp_le_exp.mpr hexponent
    _ ≤ 4 := hexpFour
    _ ≤ (27 / 16 : ℝ) ^ 4 := by norm_num

/-- Exact-target relative third moment for every fixed cooling-schedule step.
The dimension-dependent endpoint factor is uniformly worst in dimension
three, so the same constant works in every admissible dimension. -/
theorem scheduleValue_fixedRate_relativeThirdMoment_le
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hsone : scheduleValue q k ≤ 1) :
    ((∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 3) ≤
      (27 / 16 : ℝ) ^ 4 := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have ht_next : t = nextVariance q s := by
    simpa [s, t] using scheduleValue_succ q k
  have hstep : t ≤ s * (1 + 1 / (q.n : ℝ)) := by
    rw [ht_next]
    unfold nextVariance
    refine (min_le_right _ _).trans ?_
    rw [coolingRate, if_pos]
    simpa [s] using hsone
  have hstepThree : t ≤ s * (4 / 3 : ℝ) := by
    have hinv : 1 / (q.n : ℝ) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) hn
    calc
      t ≤ s * (1 + 1 / (q.n : ℝ)) := hstep
      _ ≤ s * (4 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hs.le
        linarith
  have hthree : 2 * t < 3 * s := by nlinarith
  have hraw := gaussianRatioWeight_relativeThirdMoment_le_of_oneThird
    q I (truncatedBody_gaussianPartitionOneThirdLogConcave q I)
      hs hst hthree
  have hbase := fixedRate_thirdMoment_precisionFactor_le_dimension
    hn hs hst hstep
  have hbase0 : 0 ≤ s ^ 3 / (t ^ 2 * (3 * s - 2 * t)) := by positivity
  have hpow := pow_le_pow_left₀ hbase0 hbase (q.n + 1)
  have huniform := fixedRate_thirdMoment_dimensionFactor_pow_le q.n q.dim_ok
  simpa [s, t] using hraw.trans (hpow.trans huniform)

/-- Rational `L³` constant, uniform over every admissible dimension. -/
theorem scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hsone : scheduleValue q k ≤ 1) :
    ((∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 3) ≤
      (129 / 64 : ℝ) ^ 3 := by
  exact (scheduleValue_fixedRate_relativeThirdMoment_le q I k hsone).trans
    (by norm_num)

/-- Direct `L³` form of the dimension-uniform fixed-step bound, ready for
the coordinate premise in the approximate-independence equation-(6)
estimate. -/
theorem scheduleValue_fixedRate_thirdMoment_le_rational_mean_cube
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hsone : scheduleValue q k ≤ 1) :
    let nu : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k)
    let weight := gaussianRatioWeight (n := q.n)
      (scheduleValue q k) (scheduleValue q (k + 1))
    (∫ x, weight x ^ 3 ∂nu) ≤
      ((129 / 64 : ℝ) * ∫ x, weight x ∂nu) ^ 3 := by
  dsimp only
  let mean := ∫ x, gaussianRatioWeight (scheduleValue q k)
    (scheduleValue q (k + 1)) x
      ∂(truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k) : Measure (AmbientSpace q.n))
  have hmean : 0 < mean := by
    rw [show mean = gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
        gaussianIntegral (truncatedBody q I) (scheduleValue q k) by
      simpa [mean] using gaussianRatioWeight_mean_eq q I (scheduleValue_pos q k)]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q (k + 1)))
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q k))
  have hrel := scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube
    q I k hsone
  rw [div_le_iff₀ (pow_pos hmean 3)] at hrel
  change _ ≤ ((129 / 64 : ℝ) * mean) ^ 3
  nlinarith

/-- Exact-target relative third moment for every fixed schedule step in
dimension three.  The constant `(27/16)^4` is the direct specialization of
the convex-body one-third log-concavity theorem. -/
theorem scheduleValue_fixedRate_relativeThirdMoment_le_dim_three
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hn : q.n = 3) (hsone : scheduleValue q k ≤ 1) :
    ((∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 3) ≤
      (27 / 16 : ℝ) ^ 4 := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have ht_next : t = nextVariance q s := by
    simpa [s, t] using scheduleValue_succ q k
  have hstep : t ≤ s * (1 + 1 / (3 : ℝ)) := by
    rw [ht_next]
    unfold nextVariance
    refine (min_le_right _ _).trans ?_
    rw [coolingRate, if_pos]
    · simpa [hn]
    · simpa [s] using hsone
  have hthree : 2 * t < 3 * s := by nlinarith
  have hraw := gaussianRatioWeight_relativeThirdMoment_le_of_oneThird
    q I (truncatedBody_gaussianPartitionOneThirdLogConcave q I)
      hs hst hthree
  have hbase := fixedRate_thirdMoment_precisionFactor_le hs hst hstep
  have hexponent : q.n + 1 = 4 := by omega
  rw [hexponent] at hraw
  simpa [s, t] using hraw.trans (pow_le_pow_left₀ (by positivity) hbase 4)

/-- A rational `L³` norm constant: `129/64` cubed dominates the exact
dimension-three fixed-rate relative third moment. -/
theorem scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube_dim_three
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hn : q.n = 3) (hsone : scheduleValue q k ≤ 1) :
    ((∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 3) ≤
      (129 / 64 : ℝ) ^ 3 := by
  calc
    _ ≤ (27 / 16 : ℝ) ^ 4 :=
      scheduleValue_fixedRate_relativeThirdMoment_le_dim_three q I k hn hsone
    _ ≤ (129 / 64 : ℝ) ^ 3 := by norm_num

/-- Direct `L³` form of the dimension-three bound, ready to instantiate the
coordinate premise of the approximate-independence equation-(6) theorem. -/
theorem scheduleValue_fixedRate_thirdMoment_le_rational_mean_cube_dim_three
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hn : q.n = 3) (hsone : scheduleValue q k ≤ 1) :
    let nu : Measure (AmbientSpace q.n) :=
      truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k)
    let weight := gaussianRatioWeight (n := q.n)
      (scheduleValue q k) (scheduleValue q (k + 1))
    (∫ x, weight x ^ 3 ∂nu) ≤
      ((129 / 64 : ℝ) * ∫ x, weight x ∂nu) ^ 3 := by
  dsimp only
  let mean := ∫ x, gaussianRatioWeight (scheduleValue q k)
    (scheduleValue q (k + 1)) x
      ∂(truncatedGaussianProbability q I (scheduleValue q k)
        (scheduleValue_pos q k) : Measure (AmbientSpace q.n))
  have hmean : 0 < mean := by
    rw [show mean = gaussianIntegral (truncatedBody q I) (scheduleValue q (k + 1)) /
        gaussianIntegral (truncatedBody q I) (scheduleValue q k) by
      simpa [mean] using gaussianRatioWeight_mean_eq q I (scheduleValue_pos q k)]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q (k + 1)))
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q k))
  have hrel :=
    scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube_dim_three
      q I k hn hsone
  rw [div_le_iff₀ (pow_pos hmean 3)] at hrel
  change _ ≤ ((129 / 64 : ℝ) * mean) ^ 3
  nlinarith

/-- The first two cooling transitions cannot reach the terminal variance.
This elementary lower bound supplies the factor four in the global
dependence truncation parameter. -/
theorem four_le_figureOneDependentPhaseCount (q : VolumeParams) :
    4 ≤ figureOneDependentPhaseCount q := by
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hstep : ∀ {s : ℝ}, 0 ≤ s → s ≤ 1 →
      nextVariance q s ≤ s * (4 / 3 : ℝ) := by
    intro s hs hsone
    calc
      nextVariance q s ≤ s * coolingRate q s := min_le_right _ _
      _ = s * (1 + 1 / (q.n : ℝ)) := by
        rw [coolingRate, if_pos hsone]
      _ ≤ s * (4 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hs
        have hinv : 1 / (q.n : ℝ) ≤ 1 / 3 :=
          one_div_le_one_div_of_le (by norm_num) hn
        linarith
  have hzero : scheduleValue q 0 ≤ (1 / 192 : ℝ) := by
    simp only [scheduleValue, Function.iterate_zero_apply]
    unfold initialVariance
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (q.n : ℝ))]
    nlinarith [q.heps.2]
  have hone : scheduleValue q 1 ≤ (1 / 144 : ℝ) := by
    rw [show 1 = 0 + 1 by omega, scheduleValue_succ]
    calc
      nextVariance q (scheduleValue q 0) ≤
          scheduleValue q 0 * (4 / 3 : ℝ) :=
        hstep (scheduleValue_pos q 0).le (hzero.trans (by norm_num))
      _ ≤ (1 / 192 : ℝ) * (4 / 3 : ℝ) := by gcongr
      _ = 1 / 144 := by norm_num
  have htwo : scheduleValue q 2 ≤ (1 / 108 : ℝ) := by
    rw [show 2 = 1 + 1 by omega, scheduleValue_succ]
    calc
      nextVariance q (scheduleValue q 1) ≤
          scheduleValue q 1 * (4 / 3 : ℝ) :=
        hstep (scheduleValue_pos q 1).le (hone.trans (by norm_num))
      _ ≤ (1 / 144 : ℝ) * (4 / 3 : ℝ) := by gcongr
      _ = 1 / 108 := by norm_num
  have htwoTerminal : scheduleValue q 2 < terminalVariance q :=
    htwo.trans_lt <| (by norm_num : (1 / 108 : ℝ) < 1) |>.trans_le
      (terminalVariance_ge_one' q)
  have hterminalSteps : 3 ≤ terminalPhaseSteps q := by
    by_contra hnot
    have hle : terminalPhaseSteps q ≤ 2 := by omega
    have heq := scheduleValue_terminal_persists q hle
      (scheduleValue_terminalPhaseSteps q)
    linarith
  simpa [figureOneDependentPhaseCount] using Nat.add_le_add_right hterminalSteps 1

/-- A slightly longer explicit prefix is still below variance one.  This
strengthening is useful when approximate independence has first been
transported to the exact-coordinate reset reference, which inflates its
coefficient by `5/2`. -/
theorem eight_le_figureOneDependentPhaseCount (q : VolumeParams) :
    8 ≤ figureOneDependentPhaseCount q := by
  have hn : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hstep : ∀ {s : ℝ}, 0 ≤ s → s ≤ 1 →
      nextVariance q s ≤ s * (4 / 3 : ℝ) := by
    intro s hs hsone
    calc
      nextVariance q s ≤ s * coolingRate q s := min_le_right _ _
      _ = s * (1 + 1 / (q.n : ℝ)) := by
        rw [coolingRate, if_pos hsone]
      _ ≤ s * (4 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hs
        have hinv : 1 / (q.n : ℝ) ≤ 1 / 3 :=
          one_div_le_one_div_of_le (by norm_num) hn
        linarith
  have hzero : scheduleValue q 0 ≤ (1 / 192 : ℝ) := by
    simp only [scheduleValue, Function.iterate_zero_apply]
    unfold initialVariance
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (q.n : ℝ))]
    nlinarith [q.heps.2]
  have hone : scheduleValue q 1 ≤ (1 / 144 : ℝ) := by
    rw [show 1 = 0 + 1 by omega, scheduleValue_succ]
    exact (hstep (scheduleValue_pos q 0).le (hzero.trans (by norm_num))).trans
      (by nlinarith)
  have htwo : scheduleValue q 2 ≤ (1 / 108 : ℝ) := by
    rw [show 2 = 1 + 1 by omega, scheduleValue_succ]
    exact (hstep (scheduleValue_pos q 1).le (hone.trans (by norm_num))).trans
      (by nlinarith)
  have hthree : scheduleValue q 3 ≤ (1 / 81 : ℝ) := by
    rw [show 3 = 2 + 1 by omega, scheduleValue_succ]
    exact (hstep (scheduleValue_pos q 2).le (htwo.trans (by norm_num))).trans
      (by nlinarith)
  have hfour : scheduleValue q 4 ≤ (4 / 243 : ℝ) := by
    rw [show 4 = 3 + 1 by omega, scheduleValue_succ]
    exact (hstep (scheduleValue_pos q 3).le (hthree.trans (by norm_num))).trans
      (by nlinarith)
  have hfive : scheduleValue q 5 ≤ (16 / 729 : ℝ) := by
    rw [show 5 = 4 + 1 by omega, scheduleValue_succ]
    exact (hstep (scheduleValue_pos q 4).le (hfour.trans (by norm_num))).trans
      (by nlinarith)
  have hsix : scheduleValue q 6 ≤ (64 / 2187 : ℝ) := by
    rw [show 6 = 5 + 1 by omega, scheduleValue_succ]
    exact (hstep (scheduleValue_pos q 5).le (hfive.trans (by norm_num))).trans
      (by nlinarith)
  have hsixTerminal : scheduleValue q 6 < terminalVariance q :=
    hsix.trans_lt <| (by norm_num : (64 / 2187 : ℝ) < 1) |>.trans_le
      (terminalVariance_ge_one' q)
  have hterminalSteps : 7 ≤ terminalPhaseSteps q := by
    by_contra hnot
    have hle : terminalPhaseSteps q ≤ 6 := by omega
    have heq := scheduleValue_terminal_persists q hle
      (scheduleValue_terminalPhaseSteps q)
    linarith
  simpa [figureOneDependentPhaseCount] using Nat.add_le_add_right hterminalSteps 1

/-- The final CV18 truncation parameter is at least `4096`.  This is the
numerical threshold at which the dimension-three `L³` covariance loss fits
one eighth of the executable moment slack. -/
theorem figureOneDependentAlpha_ge_4096 (q : VolumeParams) :
    (4096 : ℝ) ≤ figureOneDependentAlpha q := by
  have hm : (4 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast four_le_figureOneDependentPhaseCount q
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  rw [figureOneDependentAlpha, le_div_iff₀ (sq_pos_of_pos q.heps.1)]
  nlinarith

theorem figureOneDependentAlpha_ge_8192 (q : VolumeParams) :
    (8192 : ℝ) ≤ figureOneDependentAlpha q := by
  have hm : (8 : ℝ) ≤ figureOneDependentPhaseCount q := by
    exact_mod_cast eight_le_figureOneDependentPhaseCount q
  have he2 : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
  rw [figureOneDependentAlpha, le_div_iff₀ (sq_pos_of_pos q.heps.1)]
  nlinarith

/-- At the final CV18 parameters, the optimized `p = 3` covariance loss
with dimension-three fixed-phase norm constant `129/64` fits exactly in the
`slack/8` reserve used by the phasewise capstone. -/
theorem figureOne_fixedThirdMoment_dependence_le_slack_div_eight
    (q : VolumeParams) :
    3 * figureOneDependentEpsilon q ^ (1 / 3 : ℝ) *
        (129 / 64 : ℝ) ^ 2 ≤
      figureOneExecutableMomentSlack q / 8 := by
  let d := figureOneDependentEpsilon q ^ (1 / 3 : ℝ)
  let alpha := figureOneDependentAlpha q
  let slack := figureOneExecutableMomentSlack q
  have hepsilon : 0 < figureOneDependentEpsilon q := by
    unfold figureOneDependentEpsilon
    have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
      exact_mod_cast figureOneDependentPhaseCount_pos q
    exact div_pos (sq_pos_of_pos q.heps.1)
      (mul_pos
        (mul_pos (by norm_num) (pow_pos (figureOneDependentAlpha_pos q) 4)) hm)
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hslack0 : 0 ≤ slack / 8 := by
    exact div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
  have hdcube : d ^ 3 = figureOneDependentEpsilon q := by
    dsimp [d]
    convert Real.rpow_inv_natCast_pow hepsilon.le
      (by norm_num : (3 : ℕ) ≠ 0) using 1
    norm_num
  apply (pow_le_pow_iff_left₀
    (mul_nonneg (mul_nonneg (by norm_num) hd0) (sq_nonneg _))
    hslack0 (by norm_num : (3 : ℕ) ≠ 0)).mp
  have halpha : (4096 : ℝ) ≤ alpha := by
    simpa [alpha] using figureOneDependentAlpha_ge_4096 q
  have halphaPos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have halphaSq : (4096 : ℝ) ^ 2 ≤ alpha ^ 2 :=
    pow_le_pow_left₀ (by norm_num) halpha 2
  rw [show (3 * d * (129 / 64 : ℝ) ^ 2) ^ 3 =
      3 ^ 3 * d ^ 3 * (129 / 64 : ℝ) ^ 6 by ring,
    hdcube]
  have hdependent : figureOneDependentEpsilon q = slack / alpha ^ 4 := by
    simpa [slack, alpha] using
      figureOneDependentEpsilon_eq_slack_div_alpha_four q
  have hslack : slack = 1 / (4 * alpha) := by
    simpa [slack, alpha] using
      figureOneExecutableMomentSlack_eq_inv_four_alpha q
  rw [hdependent, hslack]
  field_simp [halphaPos.ne']
  nlinarith

/-- The same dimension-three covariance budget remains valid after the
`5/2` independence-coefficient inflation of the exact-coordinate reset
reference. -/
theorem figureOne_fixedThirdMoment_reset_dependence_le_slack_div_eight
    (q : VolumeParams) :
    3 * ((5 / 2 : ℝ) * figureOneDependentEpsilon q) ^ (1 / 3 : ℝ) *
        (129 / 64 : ℝ) ^ 2 ≤
      figureOneExecutableMomentSlack q / 8 := by
  let epsilon := (5 / 2 : ℝ) * figureOneDependentEpsilon q
  let d := epsilon ^ (1 / 3 : ℝ)
  let alpha := figureOneDependentAlpha q
  let slack := figureOneExecutableMomentSlack q
  have hdependentPos : 0 < figureOneDependentEpsilon q := by
    unfold figureOneDependentEpsilon
    have hm : (0 : ℝ) < figureOneDependentPhaseCount q := by
      exact_mod_cast figureOneDependentPhaseCount_pos q
    exact div_pos (sq_pos_of_pos q.heps.1)
      (mul_pos
        (mul_pos (by norm_num) (pow_pos (figureOneDependentAlpha_pos q) 4)) hm)
  have hepsilon : 0 < epsilon := mul_pos (by norm_num) hdependentPos
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hslack0 : 0 ≤ slack / 8 := by
    exact div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
  have hdcube : d ^ 3 = epsilon := by
    dsimp [d]
    convert Real.rpow_inv_natCast_pow hepsilon.le
      (by norm_num : (3 : ℕ) ≠ 0) using 1
    norm_num
  change 3 * d * (129 / 64 : ℝ) ^ 2 ≤ slack / 8
  apply (pow_le_pow_iff_left₀
    (mul_nonneg (mul_nonneg (by norm_num) hd0) (sq_nonneg _))
    hslack0 (by norm_num : (3 : ℕ) ≠ 0)).mp
  have halpha : (8192 : ℝ) ≤ alpha := by
    simpa [alpha] using figureOneDependentAlpha_ge_8192 q
  have halphaPos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have halphaSq : (8192 : ℝ) ^ 2 ≤ alpha ^ 2 :=
    pow_le_pow_left₀ (by norm_num) halpha 2
  rw [show (3 * d * (129 / 64 : ℝ) ^ 2) ^ 3 =
      3 ^ 3 * d ^ 3 * (129 / 64 : ℝ) ^ 6 by ring,
    hdcube]
  have hdependent : figureOneDependentEpsilon q = slack / alpha ^ 4 := by
    simpa [slack, alpha] using
      figureOneDependentEpsilon_eq_slack_div_alpha_four q
  have hslack : slack = 1 / (4 * alpha) := by
    simpa [slack, alpha] using
      figureOneExecutableMomentSlack_eq_inv_four_alpha q
  dsimp only [epsilon]
  rw [hdependent, hslack]
  field_simp [halphaPos.ne']
  nlinarith

/-- Monotone form consumed directly by any reference whose transported
dependence coefficient is bounded by `5/2` of the original allocation. -/
theorem figureOne_fixedThirdMoment_dependence_le_slack_div_eight_of_le_reset
    (q : VolumeParams) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hle : epsilon ≤ (5 / 2 : ℝ) * figureOneDependentEpsilon q) :
    3 * epsilon ^ (1 / 3 : ℝ) * (129 / 64 : ℝ) ^ 2 ≤
      figureOneExecutableMomentSlack q / 8 := by
  have hrpow := Real.rpow_le_rpow hepsilon hle (by norm_num : (0 : ℝ) ≤ 1 / 3)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrpow (by norm_num)) (sq_nonneg _)).trans
      (figureOne_fixedThirdMoment_reset_dependence_le_slack_div_eight q)

/-- The exact dependence contribution in the empirical-average second
moment (including the finite-count factor) fits the capstone reserve. -/
theorem figureOne_fixedThirdMoment_average_dependence_le_slack_div_eight
    (q : VolumeParams) {count : ℕ} (hcount : 0 < count) (mean : ℝ) :
    3 * figureOneDependentEpsilon q ^ (1 / 3 : ℝ) *
        (1 - 1 / (count : ℝ)) *
          ((129 / 64 : ℝ) * mean) ^ 2 ≤
      figureOneExecutableMomentSlack q / 8 * mean ^ 2 := by
  have hcountR : (1 : ℝ) ≤ count := by exact_mod_cast hcount
  have hcountPos : (0 : ℝ) < count := by exact_mod_cast hcount
  have hfinite0 : 0 ≤ 1 - 1 / (count : ℝ) := by
    rw [sub_nonneg, div_le_one hcountPos]
    exact hcountR
  have hfinite1 : 1 - 1 / (count : ℝ) ≤ 1 := by
    linarith [one_div_nonneg.mpr hcountPos.le]
  have hcoefficient :=
    figureOne_fixedThirdMoment_dependence_le_slack_div_eight q
  have hmeanSq : 0 ≤ mean ^ 2 := sq_nonneg mean
  have hslack0 : 0 ≤ figureOneExecutableMomentSlack q / 8 :=
    div_nonneg (figureOneExecutableMomentSlack_nonneg q) (by norm_num)
  calc
    3 * figureOneDependentEpsilon q ^ (1 / 3 : ℝ) *
          (1 - 1 / (count : ℝ)) * ((129 / 64 : ℝ) * mean) ^ 2 =
        (3 * figureOneDependentEpsilon q ^ (1 / 3 : ℝ) *
          (129 / 64 : ℝ) ^ 2) *
            (1 - 1 / (count : ℝ)) * mean ^ 2 := by ring
    _ ≤ (figureOneExecutableMomentSlack q / 8) * 1 * mean ^ 2 := by
      gcongr
    _ = figureOneExecutableMomentSlack q / 8 * mean ^ 2 := by ring

#print axioms fixedRate_thirdMoment_precisionFactor_le
#print axioms fixedRate_thirdMoment_precisionFactor_le_dimension
#print axioms fixedRate_thirdMoment_dimensionFactor_pow_le
#print axioms scheduleValue_fixedRate_relativeThirdMoment_le
#print axioms scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube
#print axioms scheduleValue_fixedRate_thirdMoment_le_rational_mean_cube
#print axioms scheduleValue_fixedRate_relativeThirdMoment_le_dim_three
#print axioms
  scheduleValue_fixedRate_relativeThirdMoment_le_rational_cube_dim_three
#print axioms
  scheduleValue_fixedRate_thirdMoment_le_rational_mean_cube_dim_three
#print axioms four_le_figureOneDependentPhaseCount
#print axioms eight_le_figureOneDependentPhaseCount
#print axioms figureOneDependentAlpha_ge_4096
#print axioms figureOneDependentAlpha_ge_8192
#print axioms figureOne_fixedThirdMoment_dependence_le_slack_div_eight
#print axioms figureOne_fixedThirdMoment_reset_dependence_le_slack_div_eight
#print axioms
  figureOne_fixedThirdMoment_dependence_le_slack_div_eight_of_le_reset
#print axioms
  figureOne_fixedThirdMoment_average_dependence_le_slack_div_eight

end ArlibCommunity.Algorithms.CV18
