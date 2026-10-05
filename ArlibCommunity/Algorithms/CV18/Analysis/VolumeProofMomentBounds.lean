/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLogConcavity

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-! # Moment bounds for executable Figure-1 weights

These bounds are stated directly for the normalized laws used by the program.
The accelerated lemma below is the radius-only bound; the sharper
phase-amortized estimate still requires the paper's localization argument.
-/

/-- Gaussian phase weights have every finite `Lᵖ` moment under the
restricted stationary law.  Compact truncation makes this explicit and lets
the canonical independent-product construction use `MemLp` directly. -/
theorem gaussianRatioWeight_memLp
    (q : VolumeParams) (I : VolumeInput q.n) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (p : ENNReal) :
    MemLp (gaussianRatioWeight (n := q.n) s t) p
      (truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n)) := by
  apply MemLp.of_bound
    (measurable_gaussianRatioWeight s t).aestronglyMeasurable
    (Real.exp (terminalVariance q / (2 * s)))
  filter_upwards [truncatedGaussianProbability_ae_mem q I hs] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (by
    unfold gaussianRatioWeight
    positivity)]
  unfold gaussianRatioWeight
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hsq := norm_sq_le_terminalVariance_of_mem_truncatedBody q I hx
  have hfirst : ‖x‖ ^ 2 / (2 * s) ≤
      terminalVariance q / (2 * s) := by
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hneg : -‖x‖ ^ 2 / (2 * t) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg ‖x‖)) (by positivity)
  calc
    -‖x‖ ^ 2 / (2 * t) - -‖x‖ ^ 2 / (2 * s) =
        ‖x‖ ^ 2 / (2 * s) + -‖x‖ ^ 2 / (2 * t) := by ring
    _ ≤ terminalVariance q / (2 * s) + 0 := add_le_add hfirst hneg
    _ = terminalVariance q / (2 * s) := by ring

/-- The terminal Gaussian-to-uniform weight likewise has every finite
`Lᵖ` moment under the truncated stationary law. -/
theorem uniformRatioWeight_memLp
    (q : VolumeParams) (I : VolumeInput q.n) {s : ℝ}
    (hs : 0 < s) (p : ENNReal) :
    MemLp (uniformRatioWeight (n := q.n) s) p
      (truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n)) := by
  apply MemLp.of_bound
    (measurable_uniformRatioWeight s).aestronglyMeasurable
    (Real.exp (terminalVariance q / (2 * s)))
  filter_upwards [truncatedGaussianProbability_ae_mem q I hs] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (by
    unfold uniformRatioWeight
    positivity)]
  unfold uniformRatioWeight
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (norm_sq_le_terminalVariance_of_mem_truncatedBody q I hx) (by positivity)

/-- The elementary numerical estimate at the end of the paper's fixed-rate
moment calculation.  Keeping it separate leaves the genuinely geometric
content isolated in the partition-function midpoint inequality below. -/
theorem fixedRate_variance_factor_le (n : ℕ) (hn : 3 ≤ n) :
    ((1 : ℝ) / (1 - 1 / (n : ℝ) ^ 2)) ^ (n + 1) ≤
      1 + 2 / (n : ℝ) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  let x : ℝ := 1 / ((n : ℝ) ^ 2 - 1)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hbase : (1 : ℝ) / (1 - 1 / (n : ℝ) ^ 2) = 1 + x := by
    dsimp [x]
    field_simp
    ring
  rw [hbase]
  calc
    (1 + x) ^ (n + 1) ≤ (Real.exp x) ^ (n + 1) := by
      gcongr
      simpa [add_comm] using Real.add_one_le_exp x
    _ = Real.exp (((n + 1 : ℕ) : ℝ) * x) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (1 / ((n : ℝ) - 1)) := by
      congr 1
      dsimp [x]
      push_cast
      field_simp [hn1.ne']
      ring
    _ ≤ (2 + 1 / ((n : ℝ) - 1)) / (2 - 1 / ((n : ℝ) - 1)) := by
      apply Real.exp_le_two_add_div_two_sub
      · exact one_div_nonneg.mpr hn1.le
      · have : 1 / ((n : ℝ) - 1) ≤ 1 / 2 := by
          apply one_div_le_one_div_of_le <;> linarith
        linarith
    _ ≤ 1 + 2 / (n : ℝ) := by
      have hden' : 0 < 2 - 1 / ((n : ℝ) - 1) := by
        have : 1 / ((n : ℝ) - 1) ≤ 1 / 2 := by
          apply one_div_le_one_div_of_le <;> linarith
        linarith
      rw [div_le_iff₀ hden']
      field_simp [hn0.ne', hn1.ne']
      nlinarith

/-- The cited weighted midpoint inequality implies the paper's sharp
fixed-rate relative-second-moment estimate.  This theorem discharges all
effective-variance and numerical algebra around `lem:z-logconcave`; proving
`GaussianPartitionMidpointLogConcave` is now the isolated geometric task. -/
theorem gaussianRatioWeight_fixedRate_relativeSecondMoment_le_of_midpoint
    (q : VolumeParams) (I : VolumeInput q.n)
    (hmidpoint : GaussianPartitionMidpointLogConcave (truncatedBody q I))
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htwo : t < 2 * s)
    (hstep : t ≤ s * (1 + 1 / (q.n : ℝ))) :
    ((∫ x, gaussianRatioWeight s t x ^ 2
        ∂(truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight s t x
        ∂(truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n))) ^ 2) ≤
      1 + 2 / (q.n : ℝ) := by
  let a : ℝ := 2 / t - 1 / s
  let b : ℝ := 1 / s
  let m : ℝ := 1 / t
  let u : ℝ := s * t / (2 * s - t)
  have ht : 0 < t := hs.trans_le hst
  have hden : 0 < 2 * s - t := by linarith
  have ha : 0 < a := by
    dsimp [a]
    rw [sub_pos, one_div_lt]
    · nlinarith
    · positivity
    · positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hau : 1 / a = u := by
    dsimp [a, u]
    field_simp [hs.ne', ht.ne', hden.ne']
  have hbs : 1 / b = s := by dsimp [b]; field_simp
  have habm : (a + b) / 2 = m := by
    dsimp [a, b, m]
    field_simp [hs.ne', ht.ne']
    ring
  have habt : 2 / (a + b) = t := by
    rw [show a + b = 2 * m by linarith [habm]]
    dsimp [m]
    field_simp [ht.ne']
  have hpartition := hmidpoint ha hb
  rw [hau, hbs, habm, habt] at hpartition
  let Zs := gaussianIntegral (truncatedBody q I) s
  let Zt := gaussianIntegral (truncatedBody q I) t
  let Zu := gaussianIntegral (truncatedBody q I) u
  have hZs : 0 < Zs := by
    simpa [Zs] using gaussianIntegral_pos q (truncatedVolumeInput q I) hs
  have hZt : 0 < Zt := by
    simpa [Zt] using gaussianIntegral_pos q (truncatedVolumeInput q I) ht
  have hZu : 0 < Zu := by
    simpa [Zu] using gaussianIntegral_pos q (truncatedVolumeInput q I) hu
  have hquotient : Zu * Zs / Zt ^ 2 ≤
      (m ^ 2 / (a * b)) ^ (q.n + 1) := by
    rw [div_le_iff₀ (sq_pos_of_pos hZt)]
    have habpow : 0 < a ^ (q.n + 1) * b ^ (q.n + 1) := by positivity
    have hraw : Zu * Zs ≤
        (m ^ (q.n + 1) * Zt) ^ 2 /
          (a ^ (q.n + 1) * b ^ (q.n + 1)) := by
      apply (le_div_iff₀ habpow).2
      change (Zu * Zs) * (a ^ (q.n + 1) * b ^ (q.n + 1)) ≤ _
      simpa [Zs, Zt, Zu, mul_assoc, mul_left_comm, mul_comm] using hpartition
    calc
      Zu * Zs ≤
          (m ^ (q.n + 1) * Zt) ^ 2 /
            (a ^ (q.n + 1) * b ^ (q.n + 1)) := hraw
      _ = (m ^ 2 / (a * b)) ^ (q.n + 1) * Zt ^ 2 := by
        simp only [div_pow, mul_pow]
        ring
  let d : ℝ := (t - s) / s
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hn : 3 ≤ q.n := q.dim_ok
  have hnR : (3 : ℝ) ≤ q.n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < q.n := by linarith
  have hdle : d ≤ 1 / (q.n : ℝ) := by
    dsimp [d]
    rw [div_le_iff₀ hs]
    nlinarith
  have hfactor_eq : m ^ 2 / (a * b) = 1 / (1 - d ^ 2) := by
    have hquad : 0 < t * (2 * s - t) := mul_pos ht hden
    calc
      m ^ 2 / (a * b) = s ^ 2 / (t * (2 * s - t)) := by
        dsimp [m, a, b]
        field_simp [hs.ne', ht.ne', hden.ne']
      _ = 1 / (1 - d ^ 2) := by
        have hdform : 1 - d ^ 2 = t * (2 * s - t) / s ^ 2 := by
          dsimp [d]
          field_simp [hs.ne']
          ring
        rw [hdform]
        field_simp [hs.ne', ht.ne', hden.ne', hquad.ne']
  have hsquares : d ^ 2 ≤ (1 / (q.n : ℝ)) ^ 2 := by
    exact (sq_le_sq₀ hd0 (one_div_nonneg.mpr hn0.le)).2 hdle
  have hendpos : 0 < 1 - (1 / (q.n : ℝ)) ^ 2 := by
    have : 1 / (q.n : ℝ) < 1 := (div_lt_one hn0).2 (by linarith)
    nlinarith [one_div_nonneg.mpr hn0.le]
  have hfactor : m ^ 2 / (a * b) ≤
      1 / (1 - 1 / (q.n : ℝ) ^ 2) := by
    rw [hfactor_eq]
    rw [show 1 / (q.n : ℝ) ^ 2 = (1 / (q.n : ℝ)) ^ 2 by ring]
    apply one_div_le_one_div_of_le hendpos
    nlinarith
  rw [gaussianRatioWeight_secondMoment_eq q I hs ht,
    gaussianRatioWeight_mean_eq q I hs]
  change (Zu / Zs) / (Zt / Zs) ^ 2 ≤ _
  have hrewrite : (Zu / Zs) / (Zt / Zs) ^ 2 = Zu * Zs / Zt ^ 2 := by
    field_simp [hZs.ne', hZt.ne']
  rw [hrewrite]
  calc
    Zu * Zs / Zt ^ 2 ≤ (m ^ 2 / (a * b)) ^ (q.n + 1) := hquotient
    _ ≤ ((1 : ℝ) / (1 - 1 / (q.n : ℝ) ^ 2)) ^ (q.n + 1) := by
      gcongr
    _ ≤ 1 + 2 / (q.n : ℝ) := fixedRate_variance_factor_le q.n q.dim_ok

/-- Conditional on the isolated partition midpoint inequality, every
fixed-rate transition of the executable clamped schedule has the sharp CV18
relative-second-moment factor. -/
theorem scheduleValue_fixedRate_relativeSecondMoment_le_of_midpoint
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hmidpoint : GaussianPartitionMidpointLogConcave (truncatedBody q I))
    (hsone : scheduleValue q k ≤ 1) :
    ((∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 2) ≤
      1 + 2 / (q.n : ℝ) := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  have hs : 0 < s := scheduleValue_pos q k
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have hnR : (3 : ℝ) ≤ q.n := by exact_mod_cast q.dim_ok
  have hn0 : (0 : ℝ) < q.n := by linarith
  have ht_next : t = nextVariance q s := by
    simpa [s, t] using scheduleValue_succ q k
  have hstep : t ≤ s * (1 + 1 / (q.n : ℝ)) := by
    rw [ht_next]
    unfold nextVariance
    refine (min_le_right _ _).trans_eq ?_
    rw [coolingRate, if_pos]
    simpa [s] using hsone
  have hfactor_lt : 1 + 1 / (q.n : ℝ) < 2 := by
    have : 1 / (q.n : ℝ) < 1 := (div_lt_one hn0).2 (by linarith)
    linarith
  have htwo : t < 2 * s := by
    calc
      t ≤ s * (1 + 1 / (q.n : ℝ)) := hstep
      _ < s * 2 := mul_lt_mul_of_pos_left hfactor_lt hs
      _ = 2 * s := by ring
  exact gaussianRatioWeight_fixedRate_relativeSecondMoment_le_of_midpoint
    q I hmidpoint hs hst htwo hstep

/-- Every fixed-rate transition of the executable schedule satisfies the
sharp CV18 relative-second-moment bound. -/
theorem scheduleValue_fixedRate_relativeSecondMoment_le
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hsone : scheduleValue q k ≤ 1) :
    ((∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 2) ≤
      1 + 2 / (q.n : ℝ) :=
  scheduleValue_fixedRate_relativeSecondMoment_le_of_midpoint q I k
    (truncatedBody_gaussianPartitionMidpointLogConcave q I) hsone

/-- A truncated accelerated step has uniformly bounded relative second
moment. This follows by applying the same radius argument to the effective
variance appearing in the exact second-moment identity. -/
theorem gaussianRatioWeight_accelerated_relativeSecondMoment_le
    (q : VolumeParams) (I : VolumeInput q.n) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (htwo : t < 2 * s)
    (hdelta : t - s ≤ s * t / (2 * terminalVariance q)) :
    ((∫ x, gaussianRatioWeight s t x ^ 2
        ∂(truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight s t x
        ∂(truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n))) ^ 2) ≤
      Real.exp (1 / 4) := by
  let u := s * t / (2 * s - t)
  have ht : 0 < t := hs.trans_le hst
  have hden : 0 < 2 * s - t := by linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have htu : t ≤ u := by
    dsimp [u]
    rw [le_div_iff₀ hden]
    nlinarith
  have hudelta : u - t ≤ t * u / (2 * terminalVariance q) := by
    have hnum := mul_le_mul_of_nonneg_left hdelta ht.le
    calc
      u - t = t * (t - s) / (2 * s - t) := by
        dsimp [u]
        field_simp [hden.ne', show s * 2 - t ≠ 0 by nlinarith]
        ring
      _ ≤ (t * (s * t / (2 * terminalVariance q))) / (2 * s - t) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = t * u / (2 * terminalVariance q) := by
        dsimp [u]
        field_simp [hden.ne', (terminalVariance_pos' q).ne']
  have hugrowth := gaussianIntegral_accelerated_le (truncatedBody q I)
    (truncatedBody_measurable q I) ht hu (terminalVariance_pos' q)
    hudelta (fun x hx => norm_sq_le_terminalVariance_of_mem_truncatedBody q I hx)
  have hmono := gaussianIntegral_mono_variance (truncatedBody q I)
    (truncatedBody_measurable q I) hs hst
  have hZs : 0 < gaussianIntegral (truncatedBody q I) s := by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I) hs
  have hZt : 0 < gaussianIntegral (truncatedBody q I) t := by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I) ht
  rw [gaussianRatioWeight_secondMoment_eq q I hs ht,
    gaussianRatioWeight_mean_eq q I hs]
  change (gaussianIntegral (truncatedBody q I) u /
      gaussianIntegral (truncatedBody q I) s) /
    (gaussianIntegral (truncatedBody q I) t /
      gaussianIntegral (truncatedBody q I) s) ^ 2 ≤ _
  rw [div_le_iff₀ (sq_pos_of_pos (div_pos hZt hZs))]
  calc
    gaussianIntegral (truncatedBody q I) u /
        gaussianIntegral (truncatedBody q I) s ≤
      (Real.exp (1 / 4) * gaussianIntegral (truncatedBody q I) t) /
        gaussianIntegral (truncatedBody q I) s := by gcongr
    _ ≤ Real.exp (1 / 4) *
        (gaussianIntegral (truncatedBody q I) t /
          gaussianIntegral (truncatedBody q I) s) ^ 2 := by
      rw [div_pow]
      field_simp [hZs.ne', hZt.ne']
      nlinarith [Real.exp_pos (1 / 4)]

/-- The radius-only second-moment estimate applies directly to every
accelerated transition of the executable first-hit schedule.  This is a
coarse constant estimate; the paper's localization lemma is needed to sharpen
it to the phase-amortized `1 + O(s / terminalVariance q)` bound. -/
theorem scheduleValue_accelerated_relativeSecondMoment_le
    (q : VolumeParams) (I : VolumeInput q.n) (k : ℕ)
    (hsone : 1 < scheduleValue q k) :
    ((∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight (scheduleValue q k) (scheduleValue q (k + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q k)
          (scheduleValue_pos q k) : Measure (AmbientSpace q.n))) ^ 2) ≤
      Real.exp (1 / 4) := by
  let s := scheduleValue q k
  let t := scheduleValue q (k + 1)
  let T := terminalVariance q
  have hs : 0 < s := scheduleValue_pos q k
  have hT : 0 < T := terminalVariance_pos' q
  have hst : s ≤ t := scheduleValue_mono q (Nat.le_add_right k 1)
  have hsT : s ≤ T := scheduleValue_le_terminal q k
  have ht_next : t = nextVariance q s := by
    simpa [s, t] using scheduleValue_succ q k
  have hraw : t ≤ s * (1 + s / (2 * T)) := by
    rw [ht_next]
    unfold nextVariance
    refine (min_le_right _ _).trans_eq ?_
    rw [coolingRate, if_neg]
    simpa [s] using not_le_of_gt hsone
  have hratio : s / (2 * T) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * T)).2
    nlinarith
  have htwo : t < 2 * s := by
    have : t ≤ 3 * s / 2 := by nlinarith
    nlinarith
  have hdelta : t - s ≤ s * t / (2 * T) := by
    have hfirst : t - s ≤ s ^ 2 / (2 * T) := by
      calc
        t - s ≤ s * (1 + s / (2 * T)) - s := by linarith
        _ = s ^ 2 / (2 * T) := by ring
    have hsquare : s ^ 2 ≤ s * t := by nlinarith
    exact hfirst.trans (div_le_div_of_nonneg_right hsquare (by positivity))
  exact gaussianRatioWeight_accelerated_relativeSecondMoment_le q I hs hst htwo
    (by simpa [T] using hdelta)

theorem gaussianIntegral_le_euclideanVolume
    (q : VolumeParams) (I : VolumeInput q.n) {s : ℝ} (hs : 0 < s) :
    gaussianIntegral (I.body : Set (AmbientSpace q.n)) s ≤ euclideanVolume I := by
  have hK : MeasurableSet (I.body : Set (AmbientSpace q.n)) :=
    I.body.isClosed.measurableSet
  rw [gaussianIntegral_eq_setIntegral hK]
  have hconst : IntegrableOn (fun _ : AmbientSpace q.n => (1 : ℝ)) I.body := by
    apply integrableOn_const
    exact I.body.isCompact.measure_lt_top.ne
    simp
  have hmono : (∫ x in (I.body : Set (AmbientSpace q.n)), gaussianDensity s x) ≤
      ∫ _x in (I.body : Set (AmbientSpace q.n)), (1 : ℝ) := by
    apply integral_mono_ae (integrable_gaussianDensity hs).integrableOn hconst
    exact Filter.Eventually.of_forall fun x => by
      unfold gaussianDensity
      apply Real.exp_le_one_iff.mpr
      have hcoeff : 0 ≤ (1 : ℝ) / (2 * s) := by positivity
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoeff)
        (sq_nonneg (‖x‖ : ℝ))
  calc
    _ ≤ ∫ _x in (I.body : Set (AmbientSpace q.n)), (1 : ℝ) := hmono
    _ = euclideanVolume I := by
      rw [setIntegral_const]
      simp [euclideanVolume, measureReal_def]

theorem uniformRatioWeight_terminal_mean_one_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    1 ≤ ∫ x, uniformRatioWeight (terminalVariance q) x
      ∂(truncatedGaussianProbability q I (terminalVariance q)
        (terminalVariance_pos' q) : Measure (AmbientSpace q.n)) := by
  rw [uniformRatioWeight_mean_eq q I (terminalVariance_pos' q)]
  have hZ : 0 < gaussianIntegral (truncatedBody q I) (terminalVariance q) := by
    simpa using gaussianIntegral_pos q (truncatedVolumeInput q I)
      (terminalVariance_pos' q)
  apply (le_div_iff₀ hZ).2
  simpa using gaussianIntegral_le_euclideanVolume q (truncatedVolumeInput q I)
    (terminalVariance_pos' q)

/-- The final Gaussian-to-uniform weight has a constant relative second
moment on the actual terminally truncated body. -/
theorem uniformRatioWeight_terminal_secondMoment_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    (∫ x, uniformRatioWeight (terminalVariance q) x ^ 2
        ∂(truncatedGaussianProbability q I (terminalVariance q)
          (terminalVariance_pos' q) : Measure (AmbientSpace q.n))) ≤
      Real.exp (1 / 2) *
        (∫ x, uniformRatioWeight (terminalVariance q) x
          ∂(truncatedGaussianProbability q I (terminalVariance q)
            (terminalVariance_pos' q) : Measure (AmbientSpace q.n))) := by
  rw [integral_truncatedGaussianProbability q I (terminalVariance_pos' q),
    uniformRatioWeight_mean_eq q I (terminalVariance_pos' q)]
  let K := truncatedBody q I
  let T := terminalVariance q
  have hK : MeasurableSet K := truncatedBody_measurable q I
  have hT : 0 < T := terminalVariance_pos' q
  have hpoint : ∀ x ∈ K,
      uniformRatioWeight T x ^ 2 * gaussianDensity T x ≤ Real.exp (1 / 2) := by
    intro x hx
    rw [uniformRatioWeight, gaussianDensity_eq, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq := norm_sq_le_terminalVariance_of_mem_truncatedBody q I hx
    have hdiv : ‖x‖ ^ 2 / (2 * T) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * T)).2
      simpa [T] using hsq
    calc
      (2 : ℝ) * (‖x‖ ^ 2 / (2 * T)) + -‖x‖ ^ 2 / (2 * T) =
          ‖x‖ ^ 2 / (2 * T) := by ring
      _ ≤ 1 / 2 := hdiv
  have hintegrable : IntegrableOn
      (fun x : AmbientSpace q.n => uniformRatioWeight T x ^ 2 * gaussianDensity T x)
      K := by
    apply ContinuousOn.integrableOn_compact
    · exact (truncatedVolumeInput q I).body.isCompact
    · unfold uniformRatioWeight gaussianDensity
      fun_prop
  have hconst : IntegrableOn (fun _ : AmbientSpace q.n => Real.exp (1 / 2)) K := by
    apply integrableOn_const
    exact (truncatedVolumeInput q I).body.isCompact.measure_lt_top.ne
    simp
  have hA : (∫ x in K, uniformRatioWeight T x ^ 2 * gaussianDensity T x) ≤
      ∫ _x in K, Real.exp (1 / 2) := by
    apply integral_mono_ae hintegrable hconst
    filter_upwards [ae_restrict_mem hK] with x hx
    exact hpoint x hx
  have hA' : (∫ x in K, uniformRatioWeight T x ^ 2 * gaussianDensity T x) ≤
      Real.exp (1 / 2) * euclideanVolume (truncatedVolumeInput q I) := by
    calc
      _ ≤ ∫ _x in K, Real.exp (1 / 2) := hA
      _ = Real.exp (1 / 2) * euclideanVolume (truncatedVolumeInput q I) := by
        rw [setIntegral_const]
        simp [euclideanVolume, K, mul_comm, measureReal_def]
  change (gaussianIntegral K T)⁻¹ *
      (∫ x in K, uniformRatioWeight T x ^ 2 * gaussianDensity T x) ≤
    Real.exp (1 / 2) *
      (euclideanVolume (truncatedVolumeInput q I) / gaussianIntegral K T)
  have hZ : 0 < gaussianIntegral K T := by
    simpa [K, T] using gaussianIntegral_pos q (truncatedVolumeInput q I) hT
  rw [div_eq_inv_mul]
  calc
    (gaussianIntegral K T)⁻¹ *
        (∫ x in K, uniformRatioWeight T x ^ 2 * gaussianDensity T x) ≤
      (gaussianIntegral K T)⁻¹ *
        (Real.exp (1 / 2) * euclideanVolume (truncatedVolumeInput q I)) := by gcongr
    _ = Real.exp (1 / 2) *
        ((gaussianIntegral K T)⁻¹ * euclideanVolume (truncatedVolumeInput q I)) := by ring
    _ = Real.exp (1 / 2) *
        (euclideanVolume (truncatedVolumeInput q I) / gaussianIntegral K T) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ Real.exp (2⁻¹ * 1) *
        (euclideanVolume (truncatedVolumeInput q I) / gaussianIntegral K T) := by norm_num

theorem uniformRatioWeight_terminal_relativeSecondMoment_le
    (q : VolumeParams) (I : VolumeInput q.n) :
    ((∫ x, uniformRatioWeight (terminalVariance q) x ^ 2
        ∂(truncatedGaussianProbability q I (terminalVariance q)
          (terminalVariance_pos' q) : Measure (AmbientSpace q.n))) /
      (∫ x, uniformRatioWeight (terminalVariance q) x
        ∂(truncatedGaussianProbability q I (terminalVariance q)
          (terminalVariance_pos' q) : Measure (AmbientSpace q.n))) ^ 2) ≤
      Real.exp (1 / 2) := by
  let mean := ∫ x, uniformRatioWeight (terminalVariance q) x
    ∂(truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n))
  let second := ∫ x, uniformRatioWeight (terminalVariance q) x ^ 2
    ∂(truncatedGaussianProbability q I (terminalVariance q)
      (terminalVariance_pos' q) : Measure (AmbientSpace q.n))
  have hm : 1 ≤ mean := uniformRatioWeight_terminal_mean_one_le q I
  have hsnd : second ≤ Real.exp (1 / 2) * mean :=
    uniformRatioWeight_terminal_secondMoment_le q I
  have hmpos : 0 < mean := zero_lt_one.trans_le hm
  change second / mean ^ 2 ≤ Real.exp (1 / 2)
  rw [div_le_iff₀ (sq_pos_of_pos hmpos)]
  calc
    second ≤ Real.exp (1 / 2) * mean := hsnd
    _ ≤ Real.exp (1 / 2) * mean ^ 2 := by
      have : mean ≤ mean ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

end ArlibCommunity.Algorithms.CV18
