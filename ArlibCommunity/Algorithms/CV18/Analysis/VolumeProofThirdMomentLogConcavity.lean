/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLogConcavity
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStationary

open MeasureTheory
open scoped ENNReal

namespace ArlibCommunity.Algorithms.CV18

/-!
# One-third Gaussian partition log-concavity

The fixed-rate phase in dimension three has no body-uniform fourth moment,
but it does have a third moment.  This file develops the `1/3, 2/3`
Prékopa--Leindler specialization needed to bound that moment.
-/

/-- The Gaussian perspective is log-concave at the weighted point with
weights `1/3` and `2/3`, in a cubed form avoiding real roots. -/
theorem gaussianPerspective_mul_sq_le_cube {n : ℕ} {K : Set (AmbientSpace n)}
    (hK : Convex ℝ K) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : AmbientSpace n) :
    gaussianPerspective K a x * gaussianPerspective K b y ^ 2 ≤
      gaussianPerspective K ((a + 2 * b) / 3)
        ((1 / 3 : ℝ) • x + (2 / 3 : ℝ) • y) ^ 3 := by
  let m : ℝ := (a + 2 * b) / 3
  let z : AmbientSpace n := (1 / 3 : ℝ) • x + (2 / 3 : ℝ) • y
  have hab : 0 < a + 2 * b := by positivity
  have hm : 0 < m := by dsimp [m]; positivity
  by_cases hx : a⁻¹ • x ∈ K
  · by_cases hy : b⁻¹ • y ∈ K
    · have hwa : 0 ≤ a / (a + 2 * b) := by positivity
      have hwb : 0 ≤ 2 * b / (a + 2 * b) := by positivity
      have hw : a / (a + 2 * b) + 2 * b / (a + 2 * b) = 1 := by
        field_simp [hab.ne']
      have hconv := hK hx hy hwa hwb hw
      have hzEq : m⁻¹ • z =
          (a / (a + 2 * b)) • (a⁻¹ • x) +
            (2 * b / (a + 2 * b)) • (b⁻¹ • y) := by
        ext i
        change m⁻¹ * ((1 / 3) * x i + (2 / 3) * y i) =
          (a / (a + 2 * b)) * (a⁻¹ * x i) +
            (2 * b / (a + 2 * b)) * (b⁻¹ * y i)
        dsimp [m]
        field_simp [ha.ne', hb.ne', hab.ne']
      have hz : m⁻¹ • z ∈ K := hzEq ▸ hconv
      unfold gaussianPerspective
      rw [Set.indicator_of_mem (show x ∈ {x | a⁻¹ • x ∈ K} from hx),
        Set.indicator_of_mem (show y ∈ {x | b⁻¹ • x ∈ K} from hy),
        Set.indicator_of_mem (show z ∈ {x | m⁻¹ • x ∈ K} from hz)]
      have htri : ‖x + (2 : ℝ) • y‖ ≤ ‖x‖ + 2 * ‖y‖ := by
        calc
          ‖x + (2 : ℝ) • y‖ ≤ ‖x‖ + ‖(2 : ℝ) • y‖ := norm_add_le _ _
          _ = ‖x‖ + 2 * ‖y‖ := by rw [norm_smul]; norm_num
      have htriSq : ‖x + (2 : ℝ) • y‖ ^ 2 ≤
          (‖x‖ + 2 * ‖y‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
      have hweighted : (‖x‖ + 2 * ‖y‖) ^ 2 ≤
          (a + 2 * b) * (‖x‖ ^ 2 / a + 2 * ‖y‖ ^ 2 / b) := by
        rw [← sub_nonneg]
        have hid :
            (a + 2 * b) * (‖x‖ ^ 2 / a + 2 * ‖y‖ ^ 2 / b) -
                (‖x‖ + 2 * ‖y‖) ^ 2 =
              2 * (b * ‖x‖ - a * ‖y‖) ^ 2 / (a * b) := by
          field_simp [ha.ne', hb.ne']
          ring
        rw [hid]
        positivity
      have hnorm : ‖x + (2 : ℝ) • y‖ ^ 2 ≤
          (a + 2 * b) * (‖x‖ ^ 2 / a + 2 * ‖y‖ ^ 2 / b) :=
        htriSq.trans hweighted
      have hzform : z = (1 / 3 : ℝ) • (x + (2 : ℝ) • y) := by
        dsimp [z]
        module
      have hzNorm : ‖z‖ ^ 2 = ‖x + (2 : ℝ) • y‖ ^ 2 / 9 := by
        rw [hzform, norm_smul]
        norm_num [Real.norm_eq_abs]
        ring
      have hexponent :
          -‖x‖ ^ 2 / (2 * a) + 2 * (-‖y‖ ^ 2 / (2 * b)) ≤
            3 * (-‖z‖ ^ 2 / (2 * m)) := by
        rw [hzNorm]
        dsimp [m]
        have hscaled : ‖x + (2 : ℝ) • y‖ ^ 2 /
              (a + 2 * b) ≤ ‖x‖ ^ 2 / a + 2 * ‖y‖ ^ 2 / b := by
          exact (div_le_iff₀ hab).2 (by simpa [mul_comm] using hnorm)
        have hlhs :
            -‖x‖ ^ 2 / (2 * a) + 2 * (-‖y‖ ^ 2 / (2 * b)) =
              -(‖x‖ ^ 2 / a + 2 * ‖y‖ ^ 2 / b) / 2 := by ring
        have hrhs :
            3 * (-(‖x + (2 : ℝ) • y‖ ^ 2 / 9) /
                (2 * ((a + 2 * b) / 3))) =
              -(‖x + (2 : ℝ) • y‖ ^ 2 / (a + 2 * b)) / 2 := by
          field_simp [hab.ne']
          ring
        rw [hlhs, hrhs]
        linarith
      have hprefactor : a * b ^ 2 ≤ m ^ 3 := by
        have hsquare : 0 ≤ (a - b) ^ 2 * (a + 8 * b) := by positivity
        dsimp [m]
        nlinarith
      rw [gaussianDensity_eq, gaussianDensity_eq, gaussianDensity_eq]
      calc
        (a * Real.exp (-‖x‖ ^ 2 / (2 * a))) *
              (b * Real.exp (-‖y‖ ^ 2 / (2 * b))) ^ 2 =
            (a * b ^ 2) * Real.exp
              (-‖x‖ ^ 2 / (2 * a) + 2 * (-‖y‖ ^ 2 / (2 * b))) := by
          rw [show 2 * (-‖y‖ ^ 2 / (2 * b)) =
            -‖y‖ ^ 2 / (2 * b) + -‖y‖ ^ 2 / (2 * b) by ring,
            Real.exp_add, Real.exp_add]
          ring
        _ ≤ m ^ 3 * Real.exp
              (-‖x‖ ^ 2 / (2 * a) + 2 * (-‖y‖ ^ 2 / (2 * b))) := by
          gcongr
        _ ≤ m ^ 3 * Real.exp (3 * (-‖z‖ ^ 2 / (2 * m))) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)
        _ = (m * Real.exp (-‖z‖ ^ 2 / (2 * m))) ^ 3 := by
          rw [show 3 * (-‖z‖ ^ 2 / (2 * m)) =
            -‖z‖ ^ 2 / (2 * m) + -‖z‖ ^ 2 / (2 * m) +
              -‖z‖ ^ 2 / (2 * m) by ring,
            Real.exp_add, Real.exp_add]
          ring
    · unfold gaussianPerspective
      rw [Set.indicator_of_notMem
        (show y ∉ {x | b⁻¹ • x ∈ K} from hy), zero_pow (by norm_num), mul_zero]
      apply pow_nonneg
      apply Set.indicator_nonneg
      intro u _hu
      exact mul_nonneg hm.le (by
        unfold gaussianDensity
        exact (Real.exp_pos _).le)
  · unfold gaussianPerspective
    rw [Set.indicator_of_notMem
      (show x ∉ {x | a⁻¹ • x ∈ K} from hx), zero_mul]
    apply pow_nonneg
    apply Set.indicator_nonneg
    intro u _hu
    exact mul_nonneg hm.le (by
      unfold gaussianDensity
      exact (Real.exp_pos _).le)

/-- ENNReal one-third-power form of the preceding cubed inequality, matching
the pointwise premise of Prékopa--Leindler at `t = 1/3`. -/
theorem gaussianPerspective_oneThirdGeomMean_le {n : ℕ}
    {K : Set (AmbientSpace n)} (hK : Convex ℝ K)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : AmbientSpace n) :
    ENNReal.ofReal (gaussianPerspective K a x) ^ ((1 : ℝ) / 3) *
        ENNReal.ofReal (gaussianPerspective K b y) ^ ((2 : ℝ) / 3) ≤
      ENNReal.ofReal (gaussianPerspective K ((a + 2 * b) / 3)
        ((1 / 3 : ℝ) • x + (2 / 3 : ℝ) • y)) := by
  let m : ℝ := (a + 2 * b) / 3
  let z : AmbientSpace n := (1 / 3 : ℝ) • x + (2 / 3 : ℝ) • y
  let A : ℝ≥0∞ := ENNReal.ofReal (gaussianPerspective K a x)
  let B : ℝ≥0∞ := ENNReal.ofReal (gaussianPerspective K b y)
  let C : ℝ≥0∞ := ENNReal.ofReal (gaussianPerspective K m z)
  have hA0 : 0 ≤ gaussianPerspective K a x :=
    gaussianPerspective_nonneg K ha.le x
  have hB0 : 0 ≤ gaussianPerspective K b y :=
    gaussianPerspective_nonneg K hb.le y
  have hm : 0 < m := by dsimp [m]; positivity
  have hC0 : 0 ≤ gaussianPerspective K m z :=
    gaussianPerspective_nonneg K hm.le z
  have hraw := gaussianPerspective_mul_sq_le_cube hK ha hb x y
  have hcubed : A * B ^ 2 ≤ C ^ 3 := by
    dsimp [A, B, C]
    rw [← ENNReal.ofReal_pow hB0, ← ENNReal.ofReal_mul hA0,
      ← ENNReal.ofReal_pow hC0]
    exact ENNReal.ofReal_le_ofReal hraw
  have htaken := ENNReal.rpow_le_rpow hcubed
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hleft : (A * B ^ 2) ^ ((1 : ℝ) / 3) =
      A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    congr 1
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    norm_num
  have hright : (C ^ 3) ^ ((1 : ℝ) / 3) = C := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  change A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) ≤ C
  rwa [hleft, hright] at htaken

/-- Prékopa--Leindler integrated at weights `1/3,2/3`. -/
theorem integral_gaussianPerspective_mul_sq_le_cube {n : ℕ}
    (K : Set (AmbientSpace n)) (hKmeas : MeasurableSet K)
    (hKconv : Convex ℝ K) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x, gaussianPerspective K a x) *
        (∫ x, gaussianPerspective K b x) ^ 2 ≤
      (∫ x, gaussianPerspective K ((a + 2 * b) / 3) x) ^ 3 := by
  let F : AmbientSpace n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (gaussianPerspective K a x)
  let G : AmbientSpace n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (gaussianPerspective K b x)
  let H : AmbientSpace n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (gaussianPerspective K ((a + 2 * b) / 3) x)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    (measurable_gaussianPerspective K hKmeas a)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp
    (measurable_gaussianPerspective K hKmeas b)
  have hH : Measurable H := ENNReal.measurable_ofReal.comp
    (measurable_gaussianPerspective K hKmeas ((a + 2 * b) / 3))
  have hone : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  have hPL : (∫⁻ x, F x) ^ ((1 : ℝ) / 3) *
        (∫⁻ y, G y) ^ ((2 : ℝ) / 3) ≤ ∫⁻ z, H z := by
    have h := prekopaLeindler_euclidean hF hG hH
      (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1)
      (fun x y => by
        rw [hone]
        exact gaussianPerspective_oneThirdGeomMean_le hKconv ha hb x y)
    rw [hone] at h
    exact h
  let A : ℝ≥0∞ := ∫⁻ x, F x
  let B : ℝ≥0∞ := ∫⁻ x, G x
  let C : ℝ≥0∞ := ∫⁻ x, H x
  have htaken := ENNReal.rpow_le_rpow hPL (by norm_num : (0 : ℝ) ≤ 3)
  have hleft :
      (A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3)) ^ (3 : ℝ) =
        A * B ^ 2 := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  have hright : C ^ (3 : ℝ) = C ^ 3 := ENNReal.rpow_natCast C 3
  have hcubeENN : A * B ^ 2 ≤ C ^ 3 := by
    change (A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3)) ^ (3 : ℝ) ≤
      C ^ (3 : ℝ) at htaken
    rwa [hleft, hright] at htaken
  have hIa := integrable_gaussianPerspective K hKmeas ha
  have hIb := integrable_gaussianPerspective K hKmeas hb
  have hm : 0 < (a + 2 * b) / 3 := by positivity
  have hIm := integrable_gaussianPerspective K hKmeas hm
  have hIa0 : 0 ≤ ∫ x, gaussianPerspective K a x :=
    integral_nonneg fun x => gaussianPerspective_nonneg K ha.le x
  have hIb0 : 0 ≤ ∫ x, gaussianPerspective K b x :=
    integral_nonneg fun x => gaussianPerspective_nonneg K hb.le x
  have hIm0 : 0 ≤ ∫ x, gaussianPerspective K ((a + 2 * b) / 3) x :=
    integral_nonneg fun x => gaussianPerspective_nonneg K hm.le x
  have hcubeLift :
      ENNReal.ofReal (∫ x, gaussianPerspective K a x) *
          ENNReal.ofReal (∫ x, gaussianPerspective K b x) ^ 2 ≤
        ENNReal.ofReal
            (∫ x, gaussianPerspective K ((a + 2 * b) / 3) x) ^ 3 := by
    simpa [A, B, C, F, G, H,
      ← ofReal_integral_eq_lintegral_ofReal hIa
        (Filter.Eventually.of_forall fun x => gaussianPerspective_nonneg K ha.le x),
      ← ofReal_integral_eq_lintegral_ofReal hIb
        (Filter.Eventually.of_forall fun x => gaussianPerspective_nonneg K hb.le x),
      ← ofReal_integral_eq_lintegral_ofReal hIm
        (Filter.Eventually.of_forall fun x => gaussianPerspective_nonneg K hm.le x)] using hcubeENN
  rw [← ENNReal.ofReal_pow hIb0, ← ENNReal.ofReal_mul hIa0,
    ← ENNReal.ofReal_pow hIm0] at hcubeLift
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcubeLift

/-- Weighted Gaussian partition log-concavity at weights `1/3,2/3`. -/
def GaussianPartitionOneThirdLogConcave {n : ℕ}
    (K : Set (AmbientSpace n)) : Prop :=
  ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b →
    (a ^ (n + 1) * gaussianIntegral K (1 / a)) *
        (b ^ (n + 1) * gaussianIntegral K (1 / b)) ^ 2 ≤
      (((a + 2 * b) / 3) ^ (n + 1) *
        gaussianIntegral K (3 / (a + 2 * b))) ^ 3

/-- Prékopa--Leindler proves weighted one-third Gaussian partition
log-concavity for every measurable convex set. -/
theorem gaussianPartitionOneThirdLogConcave {n : ℕ}
    (K : Set (AmbientSpace n)) (hKmeas : MeasurableSet K)
    (hKconv : Convex ℝ K) : GaussianPartitionOneThirdLogConcave K := by
  intro a b ha hb
  have hm : 0 < (a + 2 * b) / 3 := by positivity
  have h := integral_gaussianPerspective_mul_sq_le_cube
    K hKmeas hKconv ha hb
  rw [integral_gaussianPerspective_eq K ha,
    integral_gaussianPerspective_eq K hb,
    integral_gaussianPerspective_eq K hm] at h
  have hvariance : 1 / ((a + 2 * b) / 3) = 3 / (a + 2 * b) := by
    field_simp [(by positivity : 0 < a + 2 * b).ne']
  rw [hvariance] at h
  exact h

theorem truncatedBody_gaussianPartitionOneThirdLogConcave
    (q : VolumeParams) (I : VolumeInput q.n) :
    GaussianPartitionOneThirdLogConcave (truncatedBody q I) :=
  gaussianPartitionOneThirdLogConcave (truncatedBody q I)
    (truncatedBody_measurable q I) (truncatedVolumeInput q I).body.convex

/-- The one-third partition inequality bounds the relative third moment by
the explicit precision-ratio factor. -/
theorem gaussianRatioWeight_relativeThirdMoment_le_of_oneThird
    (q : VolumeParams) (I : VolumeInput q.n)
    (honeThird : GaussianPartitionOneThirdLogConcave (truncatedBody q I))
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (hthree : 2 * t < 3 * s) :
    ((∫ x, gaussianRatioWeight s t x ^ 3
        ∂(truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n))) /
      (∫ x, gaussianRatioWeight s t x
        ∂(truncatedGaussianProbability q I s hs : Measure (AmbientSpace q.n))) ^ 3) ≤
      (s ^ 3 / (t ^ 2 * (3 * s - 2 * t))) ^ (q.n + 1) := by
  let a : ℝ := 3 / t - 2 / s
  let b : ℝ := 1 / s
  let m : ℝ := 1 / t
  let u : ℝ := s * t / (3 * s - 2 * t)
  have ht : 0 < t := hs.trans_le hst
  have hden : 0 < 3 * s - 2 * t := by linarith
  have ha : 0 < a := by
    dsimp [a]
    rw [sub_pos]
    apply (div_lt_div_iff₀ hs ht).2
    nlinarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hau : 1 / a = u := by
    dsimp [a, u]
    field_simp [hs.ne', ht.ne', hden.ne']
  have hbs : 1 / b = s := by dsimp [b]; field_simp
  have habm : (a + 2 * b) / 3 = m := by
    dsimp [a, b, m]
    field_simp [hs.ne', ht.ne']
    ring
  have habt : 3 / (a + 2 * b) = t := by
    rw [show a + 2 * b = 3 * m by linarith [habm]]
    dsimp [m]
    field_simp [ht.ne']
  have hpartition := honeThird ha hb
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
  have hquotient : Zu * Zs ^ 2 / Zt ^ 3 ≤
      (m ^ 3 / (a * b ^ 2)) ^ (q.n + 1) := by
    rw [div_le_iff₀ (pow_pos hZt 3)]
    have habpow : 0 < a ^ (q.n + 1) * (b ^ (q.n + 1)) ^ 2 := by positivity
    have hraw : Zu * Zs ^ 2 ≤
        (m ^ (q.n + 1) * Zt) ^ 3 /
          (a ^ (q.n + 1) * (b ^ (q.n + 1)) ^ 2) := by
      apply (le_div_iff₀ habpow).2
      change (a ^ (q.n + 1) * Zu) *
          (b ^ (q.n + 1) * Zs) ^ 2 ≤
        (m ^ (q.n + 1) * Zt) ^ 3 at hpartition
      calc
        (Zu * Zs ^ 2) *
              (a ^ (q.n + 1) * (b ^ (q.n + 1)) ^ 2) =
            (a ^ (q.n + 1) * Zu) *
              (b ^ (q.n + 1) * Zs) ^ 2 := by ring
        _ ≤ (m ^ (q.n + 1) * Zt) ^ 3 := hpartition
    calc
      Zu * Zs ^ 2 ≤
          (m ^ (q.n + 1) * Zt) ^ 3 /
            (a ^ (q.n + 1) * (b ^ (q.n + 1)) ^ 2) := hraw
      _ = (m ^ 3 / (a * b ^ 2)) ^ (q.n + 1) * Zt ^ 3 := by
        simp only [div_pow, mul_pow]
        ring
  rw [gaussianRatioWeight_thirdMoment_eq q I hs ht,
    gaussianRatioWeight_mean_eq q I hs]
  change (Zu / Zs) / (Zt / Zs) ^ 3 ≤ _
  have hrewrite : (Zu / Zs) / (Zt / Zs) ^ 3 = Zu * Zs ^ 2 / Zt ^ 3 := by
    field_simp [hZs.ne', hZt.ne']
  rw [hrewrite]
  have hfactor : m ^ 3 / (a * b ^ 2) =
      s ^ 3 / (t ^ 2 * (3 * s - 2 * t)) := by
    dsimp [m, a, b]
    field_simp [hs.ne', ht.ne', hden.ne']
  rwa [hfactor] at hquotient

#print axioms gaussianPerspective_mul_sq_le_cube
#print axioms gaussianPerspective_oneThirdGeomMean_le
#print axioms integral_gaussianPerspective_mul_sq_le_cube
#print axioms gaussianPartitionOneThirdLogConcave
#print axioms truncatedBody_gaussianPartitionOneThirdLogConcave
#print axioms gaussianRatioWeight_relativeThirdMoment_le_of_oneThird

end ArlibCommunity.Algorithms.CV18
