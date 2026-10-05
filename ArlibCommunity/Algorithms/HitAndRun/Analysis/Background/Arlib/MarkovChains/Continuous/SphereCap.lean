/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunOverlap
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The spherical-cap estimate: `σ{θ : √n·|⟨θ,w⟩| > |w|} ≤ 9/25`, and Lemma 4.1 with no hypotheses

This file closes the **last inline hypothesis** of Lovász–Vempala's Lemma 4.1 as formalised in
`Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean`: the spherical-cap estimate `hcap`,
which that file records as "the one remaining unproved input" and which
`Arlib/MarkovChains/Continuous/SphereCoord.lean` reduces to a statement about the sphere
alone.  The headline is

* `Arlib.MarkovChains.unifSphere_cap_le` — for `n ≥ 1100`,
  `σ{θ ∈ Sⁿ⁻¹ : √n·|⟨θ,w⟩| > |w|} ≤ 9/25 = 0.36`;
* `Arlib.MarkovChains.hitAndRun_almostOrthogonal_le_nine_twentyfifths` — the same bound in the
  exact shape of the `hcap` binder of `tvLe_hitAndRun_lemma41`;
* `Arlib.MarkovChains.tvLe_hitAndRun_lemma41_uncond` — **Lemma 4.1 with every hypothesis of
  the paper's proof discharged**, concluding `TVLe (P_u) (P_v) (1 − 1/8000)`.

## What had to be proved, and why it is not cheap

The threshold `n^{-1/2}` is *exactly* the root-mean-square value of `⟨θ,w⟩`
(`Arlib.MarkovChains.finrank_mul_lintegral_inner_sq`), so the event is a **central** one, not a
tail.  Chebyshev, Chernoff and every pure moment bound are trivial there — two moments alone
permit `P(X ≥ E X)` arbitrarily close to `1` — and the two pigeonhole bounds `1/n` and
`1 − 1/n` of `SphereCoord.lean` are the best that `∑ᵢ ⟨θ,eᵢ⟩² = 1` alone gives.  Something
that sees the actual distribution is unavoidable.  The route taken here is:

1. **The cap is a cone, and a cone does not care which rotation-invariant measure measures it**
   (`lintegral_gauss_cone`).  A layer-cake decomposition plus the dilation law
   `vol(C ∩ B_R) = Rⁿ·vol(C ∩ B₁)` (`volume_cone_inter_sqLt`) gives, for *every* measurable
   cone `C`, `∫_C e^{−‖x‖²/2} dx = vol(C ∩ B₁)·κ_n` with a radial factor `κ_n` independent of
   `C`.  So the normalised Lebesgue measure of `C ∩ B₁` equals the Gaussian measure of `C`
   (`volume_cone_inter_le_of_lintegral_le`).  This is the step that buys **independence**: the
   Gaussian weight is a product measure.
2. **A union bound in the Gaussian picture** (`lintegral_gauss_cone_le`).  On the cone
   `{‖x‖² < n·x₀²}` either `|x₀| ≥ c` or `∑_{i≠0} xᵢ² < (n−1)c²`.  The first event has Gaussian
   mass `2(1 − Φ(c))`, computed honestly by integrating the degree-10 Taylor polynomial of
   `e^{−t²/2}` against the exact `∫ℝ e^{−t²/2} = √(2π)` (`gauss_tail_le`, `poly_le_gauss`);
   the second is a `χ²` lower-tail, bounded by the exponential moment
   `E e^{−λ Z²} = (1+2λ)^{−1/2}` coordinate by coordinate (`lintegral_gauss_shell_le`).
3. **Numbers.**  At `c = 23/25` and `λ = 9/100` the head integrates to at least `1.6103`, so
   the slab piece is at most `1 − 1.6103/√(2π) ≤ 0.3576`; the Chernoff piece is `βⁿ⁻¹` with
   `β = e^{λc²}/√(1+2λ) ≤ 0.994`, hence at most `0.0022` once `n − 1 ≥ 1099`.  Total: `0.36`.

## Honest scope

* **The bound is `0.36`, not the sharp `0.31731…`.**  The union bound of step 2 costs about
  `0.04`; recovering the sharp constant needs the density `(1−t²)^{(n−3)/2}` of `⟨θ,ŵ⟩`, which
  Mathlib v4.32 does not have and which this file does not build.
* **The threshold is `n ≥ 1100`, and it is an artifact of the method, not of the statement.**
  The estimate `σ ≤ 0.36` is in fact true from about `n = 8` on (the true value is `0.363` at
  `n = 6` and `0.351` at `n = 8`), and `q₂ < 3/8` from `n = 5` on; for `n ≤ 4` it is false
  (`q₂ ≥ 0.391`), so *some* dimension hypothesis is
  mandatory (`q₂(2) = 1/2`, `q₂(3) = 0.4226…`).  What forces `1100` here is that the Chernoff
  piece decays like `0.994ⁿ`, and `c` cannot be pushed towards `1` without inflating it.
* **Consequently the constant of Lemma 4.1 is `1 − 1/8000`**, against the `1 − 1/1892.8…` that
  a sharp cap bound would give with the corrected `A₃`, and against the paper's `1 − 1/500`,
  which `HitAndRunOverlap.lean` shows is not attainable at all.
* **Non-vacuity.**  The bounded quantity is not zero: `SphereCoord.lean`'s
  `inv_le_unifSphere_almostOrthogonalDirClosed` gives `σ ≥ 1/n > 0` for the closed cap, so
  `unifSphere_cap_le` is a genuine two-sided sandwich, and the `hcap` binder it discharges is
  the one `tvLe_hitAndRun_lemma41` actually consumes (it is passed by `exact`).
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric Module Set
open scoped ENNReal Pointwise RealInnerProductSpace

section Cone

variable {n : ℕ}

/-- The open Euclidean ball of `Fin n → ℝ`, written without the Euclidean norm (the norm of
`Fin n → ℝ` is the supremum norm, so the ball has to be spelled out). -/
theorem measurableSet_sqLt (n : ℕ) (R : ℝ) :
    MeasurableSet {x : Fin n → ℝ | ∑ i, x i ^ 2 < R} := by
  have h : Continuous fun x : Fin n → ℝ => ∑ i, x i ^ 2 := by fun_prop
  exact measurableSet_lt h.measurable measurable_const

/-- Dilating the unit ball. -/
theorem smul_sqLt_one {R : ℝ} (hR : 0 < R) (n : ℕ) :
    R • {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1} = {x : Fin n → ℝ | ∑ i, x i ^ 2 < R ^ 2} := by
  have key : ∀ (r : ℝ) (y : Fin n → ℝ), ∑ i, (r • y) i ^ 2 = r ^ 2 * ∑ i, y i ^ 2 := by
    intro r y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp [Pi.smul_apply, smul_eq_mul, mul_pow]
  ext x
  simp only [Set.mem_smul_set, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [key]
    nlinarith [pow_pos hR 2]
  · intro hx
    refine ⟨R⁻¹ • x, ?_, ?_⟩
    · rw [key, inv_pow, inv_mul_lt_iff₀ (by positivity), mul_one]
      exact hx
    · rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

/-- A cone meets the ball of radius `R` in a dilate of its intersection with the unit ball. -/
theorem volume_cone_inter_sqLt {C : Set (Fin n → ℝ)} (hn : n ≠ 0)
    (hcone : ∀ r : ℝ, 0 < r → r • C = C) {R : ℝ} (hR : 0 ≤ R) :
    volume (C ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < R ^ 2})
      = ENNReal.ofReal (R ^ n) * volume (C ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1}) := by
  rcases eq_or_lt_of_le hR with h | hRpos
  · subst_vars
    have hempty : {x : Fin n → ℝ | ∑ i, x i ^ 2 < (0 : ℝ) ^ 2} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg (x i))
    rw [hempty, Set.inter_empty, measure_empty, zero_pow hn, ENNReal.ofReal_zero, zero_mul]
  · have hCR : C ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < R ^ 2}
        = R • (C ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1}) := by
      rw [Set.smul_set_inter₀ (by exact_mod_cast hRpos.ne'), hcone R hRpos, smul_sqLt_one hRpos]
    rw [hCR, Measure.addHaar_smul]
    congr 1
    · rw [finrank_pi_fintype ℝ (ι := Fin n)]
      simp only [finrank_self, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
        Fintype.card_fin]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ R ^ n)]

/-! ### The layer-cake identity for a cone -/

/-- The radius of the level set `{x : t < exp (-‖x‖²/2)}`. -/
noncomputable def gaussRadius (t : ℝ) : ℝ := Real.sqrt (2 * Real.log (1 / t))

theorem gaussRadius_nonneg (t : ℝ) : 0 ≤ gaussRadius t := Real.sqrt_nonneg _

theorem measurable_gaussRadius : Measurable gaussRadius :=
  Measurable.sqrt
    (measurable_const.mul (Real.measurable_log.comp (measurable_const.div measurable_id)))

/-- The level sets of the Gaussian are the Euclidean balls of radius `gaussRadius t`. -/
theorem lt_exp_iff_lt_gaussRadius_sq {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 ≤ s) :
    t < Real.exp (-s / 2) ↔ s < gaussRadius t ^ 2 := by
  have hlog : Real.log (1 / t) = -Real.log t := by
    rw [one_div, Real.log_inv]
  rcases le_or_gt t 1 with hle | hgt
  · have hlt0 : Real.log t ≤ 0 := Real.log_nonpos ht.le hle
    have hsq : gaussRadius t ^ 2 = -(2 * Real.log t) := by
      rw [gaussRadius, Real.sq_sqrt (by rw [hlog]; linarith), hlog]
      ring
    rw [hsq, ← Real.log_lt_iff_lt_exp ht]
    constructor
    · intro h; linarith
    · intro h; linarith
  · have hlt0 : 0 < Real.log t := Real.log_pos hgt
    have hsq : gaussRadius t ^ 2 = 0 := by
      have : gaussRadius t = 0 := by
        rw [gaussRadius]
        exact Real.sqrt_eq_zero_of_nonpos (by rw [hlog]; linarith)
      rw [this]; ring
    rw [hsq]
    refine iff_of_false (not_lt.2 ?_) (not_lt.2 hs)
    calc Real.exp (-s / 2) ≤ Real.exp 0 := by
          exact Real.exp_le_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
      _ ≤ t := hgt.le

/-- The common radial factor of the layer-cake decomposition.  It is *only* a name for this
integral: nothing here evaluates it (in closed form it is a Gamma factor, which is **not**
proved below and is never used), because it cancels in every ratio.  All that is needed is
that it is neither `0` nor `⊤`, and that is derived from the case `C = univ` inside
`volume_cone_inter_le_of_lintegral_le`. -/
noncomputable def coneNormalizer (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (gaussRadius t ^ n)

/-- **The layer-cake identity for a cone.**  For every measurable cone `C` — a set with
`r • C = C` for all `r > 0` — the Gaussian integral over `C` is the volume of `C ∩ B₁` times a
factor that does not depend on `C`.  Consequently the *normalised* Gaussian measure of a cone
and the *normalised* Lebesgue measure of its trace on the unit ball agree. -/
theorem lintegral_gauss_cone (hn : n ≠ 0) {C : Set (Fin n → ℝ)}
    (hcone : ∀ r : ℝ, 0 < r → r • C = C) :
    ∫⁻ x in C, ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))
      = volume (C ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1}) * coneNormalizer n := by
  have hmeas : Measurable fun x : Fin n → ℝ => Real.exp (-(∑ i, x i ^ 2) / 2) := by fun_prop
  rw [lintegral_eq_lintegral_meas_lt (volume.restrict C)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hmeas.aemeasurable,
    coneNormalizer,
    ← lintegral_const_mul _ (measurable_gaussRadius.pow_const n).ennreal_ofReal]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hset : {x : Fin n → ℝ | t < Real.exp (-(∑ i, x i ^ 2) / 2)}
      = {x : Fin n → ℝ | ∑ i, x i ^ 2 < gaussRadius t ^ 2} := by
    ext x
    exact lt_exp_iff_lt_gaussRadius_sq ht (Finset.sum_nonneg fun i _ => sq_nonneg (x i))
  rw [Measure.restrict_apply (by rw [hset]; exact measurableSet_sqLt n _), hset,
    Set.inter_comm, volume_cone_inter_sqLt hn hcone (gaussRadius_nonneg t), mul_comm]

/-- The inner box shows the unit ball has positive volume; that is all that is needed to
cancel `coneNormalizer` in a ratio. -/
theorem volume_sqLt_one_pos (hn : n ≠ 0) :
    0 < volume {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1} := by
  have hnR : (0 : ℝ) < n := by positivity
  set a : ℝ := Real.sqrt (1 / (2 * n)) with ha
  have hapos : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hasq : a ^ 2 = 1 / (2 * n) := Real.sq_sqrt (by positivity)
  have hsub : (Set.univ.pi fun _ : Fin n => Set.Ioo (-a) a)
      ⊆ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1} := by
    intro x hx
    have hxi : ∀ i, x i ^ 2 ≤ a ^ 2 := by
      intro i
      have := hx i (Set.mem_univ i)
      simp only [Set.mem_Ioo] at this
      nlinarith [this.1, this.2]
    have : ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, a ^ 2 :=
      Finset.sum_le_sum fun i _ => hxi i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hasq] at this
    have hlt : (n : ℝ) * (1 / (2 * n)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    exact lt_of_le_of_lt this hlt
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [volume_pi_pi]
  simp only [Real.volume_Ioo, sub_neg_eq_add]
  refine pos_iff_ne_zero.2 ?_
  rw [Finset.prod_ne_zero_iff]
  exact fun i _ => (ENNReal.ofReal_pos.2 (by linarith)).ne'

end Cone

/-! ## The Gaussian weight as a product measure -/

section Gaussian

variable {n : ℕ}

/-- Fubini for a product integrand on `Fin n → ℝ`, in `ℝ≥0∞` form. -/
theorem lintegral_ofReal_prod (n : ℕ) (f : Fin n → ℝ → ℝ) (hf0 : ∀ i t, 0 ≤ f i t)
    (hfi : ∀ i, Integrable (f i)) :
    ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (∏ i, f i (x i)) = ENNReal.ofReal (∏ i, ∫ t, f i t) := by
  rw [← integral_fintype_prod_volume_eq_prod]
  refine (ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun x =>
    Finset.prod_nonneg fun i _ => hf0 i (x i))).symm
  have h : Integrable (fun x : Fin n → ℝ => ∏ i, f i (x i)) (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (fun i => hfi i)
  rwa [← volume_pi] at h

theorem integrable_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * t ^ 2)) := integrable_exp_neg_mul_sq hb

theorem integrable_gauss_half : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) := by
  have h := integrable_gauss (b := 1 / 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  ring_nf

theorem integral_gauss_half : ∫ t : ℝ, Real.exp (-(t ^ 2) / 2) = Real.sqrt (2 * Real.pi) := by
  have h := integral_gaussian (1 / 2 : ℝ)
  have hf : (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2))
      = fun t : ℝ => Real.exp (-(t ^ 2) / 2) := by
    funext t
    congr 1
    ring
  rw [hf] at h
  rw [h, show Real.pi / (1 / 2) = 2 * Real.pi by ring]

/-- The Gaussian weight splits as a product over the coordinates. -/
theorem exp_sum_sq (n : ℕ) (x : Fin n → ℝ) :
    Real.exp (-(∑ i, x i ^ 2) / 2) = ∏ i, Real.exp (-(x i ^ 2) / 2) := by
  rw [← Real.exp_sum]
  congr 1
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The total Gaussian mass.** -/
theorem lintegral_gauss_univ (n : ℕ) :
    ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi) ^ n) := by
  simp only [exp_sum_sq]
  rw [lintegral_ofReal_prod n (fun _ t => Real.exp (-(t ^ 2) / 2))
      (fun _ t => (Real.exp_pos _).le) (fun _ => integrable_gauss_half)]
  simp only [integral_gauss_half, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The two pieces of the union bound -/

/-- **The slab complement.**  The Gaussian mass of `{|x₀| ≥ c}` factors as a one-dimensional
tail times the mass of the remaining `m` coordinates. -/
theorem lintegral_gauss_slab (m : ℕ) (c : ℝ) :
    ∫⁻ x : Fin (m + 1) → ℝ, Set.indicator {x : Fin (m + 1) → ℝ | c ≤ |x 0|}
        (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))) x
      = ENNReal.ofReal ((∫ t : ℝ, Set.indicator {t : ℝ | c ≤ |t|}
          (fun t => Real.exp (-(t ^ 2) / 2)) t) * Real.sqrt (2 * Real.pi) ^ m) := by
  have hSm : MeasurableSet {t : ℝ | c ≤ |t|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  set g₀ : ℝ → ℝ := Set.indicator {t : ℝ | c ≤ |t|} (fun t => Real.exp (-(t ^ 2) / 2)) with hg₀
  set g₁ : ℝ → ℝ := fun t => Real.exp (-(t ^ 2) / 2) with hg₁
  set f : Fin (m + 1) → ℝ → ℝ := Fin.cons g₀ (fun _ => g₁) with hf
  have hf0 : ∀ i t, 0 ≤ f i t := by
    intro i t
    refine Fin.cases ?_ ?_ i
    · simp only [hf, Fin.cons_zero, hg₀]
      exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) t
    · intro j
      simp only [hf, Fin.cons_succ, hg₁]
      exact (Real.exp_pos _).le
  have hfi : ∀ i, Integrable (f i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa only [hf, Fin.cons_zero, hg₀] using integrable_gauss_half.indicator hSm
    · intro j
      simpa only [hf, Fin.cons_succ, hg₁] using integrable_gauss_half
  have key : ∀ x : Fin (m + 1) → ℝ,
      Set.indicator {x : Fin (m + 1) → ℝ | c ≤ |x 0|}
        (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))) x
        = ENNReal.ofReal (∏ i, f i (x i)) := by
    intro x
    have hprod : ∏ i, f i (x i) = g₀ (x 0) * ∏ j : Fin m, g₁ (x j.succ) := by
      rw [Fin.prod_univ_succ]
      simp only [hf, Fin.cons_zero, Fin.cons_succ]
    by_cases hx : x ∈ {x : Fin (m + 1) → ℝ | c ≤ |x 0|}
    · rw [Set.indicator_of_mem hx, hprod, hg₀,
        Set.indicator_of_mem (show x 0 ∈ {t : ℝ | c ≤ |t|} from hx)]
      congr 1
      rw [exp_sum_sq, Fin.prod_univ_succ]
    · rw [Set.indicator_of_notMem hx, hprod, hg₀,
        Set.indicator_of_notMem (show x 0 ∉ {t : ℝ | c ≤ |t|} from hx), zero_mul,
        ENNReal.ofReal_zero]
  simp only [key]
  rw [lintegral_ofReal_prod (m + 1) f hf0 hfi, Fin.prod_univ_succ]
  simp only [hf, Fin.cons_zero, Fin.cons_succ, hg₁, integral_gauss_half, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- **The Chernoff piece.**  The Gaussian mass of the event that the last `m` coordinates have
small square sum is bounded by an exponential moment. -/
theorem lintegral_gauss_shell_le (m : ℕ) {c lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ x : Fin (m + 1) → ℝ,
        Set.indicator {x : Fin (m + 1) → ℝ | ∑ j : Fin m, x j.succ ^ 2 < m * c ^ 2}
          (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))) x
      ≤ ENNReal.ofReal (Real.exp (lam * ((m : ℝ) * c ^ 2)) * Real.sqrt (2 * Real.pi)
          * Real.sqrt (Real.pi / (lam + 1 / 2)) ^ m) := by
  set K : ℝ := Real.exp (lam * ((m : ℝ) * c ^ 2)) with hK
  set g₀ : ℝ → ℝ := fun t => K * Real.exp (-(t ^ 2) / 2) with hg₀
  set g₁ : ℝ → ℝ := fun t => Real.exp (-(lam + 1 / 2) * t ^ 2) with hg₁
  set f : Fin (m + 1) → ℝ → ℝ := Fin.cons g₀ (fun _ => g₁) with hf
  have hf0 : ∀ i t, 0 ≤ f i t := by
    intro i t
    refine Fin.cases ?_ ?_ i
    · simp only [hf, Fin.cons_zero, hg₀]
      positivity
    · intro j
      simp only [hf, Fin.cons_succ, hg₁]
      exact (Real.exp_pos _).le
  have hfi : ∀ i, Integrable (f i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa only [hf, Fin.cons_zero, hg₀] using integrable_gauss_half.const_mul K
    · simpa only [hf, Fin.cons_succ, hg₁] using
        fun _ => integrable_gauss (b := lam + 1 / 2) (by linarith)
  have key : ∀ x : Fin (m + 1) → ℝ,
      Set.indicator {x : Fin (m + 1) → ℝ | ∑ j : Fin m, x j.succ ^ 2 < m * c ^ 2}
        (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))) x
        ≤ ENNReal.ofReal (∏ i, f i (x i)) := by
    intro x
    have hprodj : ∏ _j : Fin m, Real.exp (-(lam + 1 / 2) * x _j.succ ^ 2)
        = Real.exp (-(lam + 1 / 2) * ∑ j : Fin m, x j.succ ^ 2) := by
      rw [← Real.exp_sum, Finset.mul_sum]
    have hprod : ∏ i, f i (x i) = K * Real.exp (-(x 0 ^ 2) / 2)
        * Real.exp (-(lam + 1 / 2) * ∑ j : Fin m, x j.succ ^ 2) := by
      rw [Fin.prod_univ_succ]
      simp only [hf, Fin.cons_zero, Fin.cons_succ, hg₀, hg₁]
      rw [hprodj]
    by_cases hx : x ∈ {x : Fin (m + 1) → ℝ | ∑ j : Fin m, x j.succ ^ 2 < m * c ^ 2}
    · rw [Set.indicator_of_mem hx, hprod, hK]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hS : ∑ j : Fin m, x j.succ ^ 2 < (m : ℝ) * c ^ 2 := hx
      have hsum : ∑ i, x i ^ 2 = x 0 ^ 2 + ∑ j : Fin m, x j.succ ^ 2 := Fin.sum_univ_succ _
      rw [hsum]
      nlinarith [hlam, hS]
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  refine le_trans (lintegral_mono key) ?_
  rw [lintegral_ofReal_prod (m + 1) f hf0 hfi, Fin.prod_univ_succ]
  simp only [hf, Fin.cons_zero, Fin.cons_succ, hg₀, hg₁, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [integral_const_mul, integral_gauss_half, integral_gaussian]

/-- The whole space is a cone. -/
theorem smul_univ_eq (n : ℕ) {r : ℝ} (hr : 0 < r) :
    r • (Set.univ : Set (Fin n → ℝ)) = Set.univ := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_univ, iff_true]
  exact ⟨r⁻¹ • x, trivial, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩

/-- **From the Gaussian ratio to the Lebesgue ratio.**  This is the payoff of
`lintegral_gauss_cone`: for a cone, a bound on the *Gaussian* mass is a bound on the fraction
of the unit ball it occupies.  The radial factor `coneNormalizer` cancels. -/
theorem volume_cone_inter_le_of_lintegral_le (hn : n ≠ 0) {C : Set (Fin n → ℝ)}
    (hcone : ∀ r : ℝ, 0 < r → r • C = C) {q : ℝ}
    (h : ∫⁻ x in C, ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))
      ≤ ENNReal.ofReal q * ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))) :
    volume (C ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1})
      ≤ ENNReal.ofReal q * volume {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1} := by
  have huniv := lintegral_gauss_cone (n := n) hn (C := Set.univ) (fun r hr => smul_univ_eq n hr)
  rw [Measure.restrict_univ, Set.univ_inter, lintegral_gauss_univ n] at huniv
  have hVpos : 0 < volume {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1} := volume_sqLt_one_pos hn
  have hpos : (0 : ℝ) < Real.sqrt (2 * Real.pi) ^ n := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hk0 : coneNormalizer n ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at huniv
    exact absurd huniv.symm (ENNReal.ofReal_pos.2 hpos).ne
  have hktop : coneNormalizer n ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hVpos.ne'] at huniv
    exact absurd huniv ENNReal.ofReal_ne_top
  rw [lintegral_gauss_cone hn hcone, lintegral_gauss_univ n, huniv, ← mul_assoc] at h
  have h2 := mul_le_mul_left h (coneNormalizer n)⁻¹
  rwa [mul_assoc, mul_assoc, ENNReal.mul_inv_cancel hk0 hktop, mul_one, mul_one] at h2

/-- **The union bound for the cone.**  Every point of the cone either has a large first
coordinate or has small remaining coordinates. -/
theorem lintegral_gauss_cone_le (m : ℕ) {c lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ x in {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < ((m : ℝ) + 1) * x 0 ^ 2},
        ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))
      ≤ ENNReal.ofReal ((∫ t : ℝ, Set.indicator {t : ℝ | c ≤ |t|}
            (fun t => Real.exp (-(t ^ 2) / 2)) t) * Real.sqrt (2 * Real.pi) ^ m)
        + ENNReal.ofReal (Real.exp (lam * ((m : ℝ) * c ^ 2)) * Real.sqrt (2 * Real.pi)
            * Real.sqrt (Real.pi / (lam + 1 / 2)) ^ m) := by
  have hCm : MeasurableSet {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < ((m : ℝ) + 1) * x 0 ^ 2} := by
    have h1 : Continuous fun x : Fin (m + 1) → ℝ => ∑ i, x i ^ 2 := by fun_prop
    have h2 : Continuous fun x : Fin (m + 1) → ℝ => ((m : ℝ) + 1) * x 0 ^ 2 := by fun_prop
    exact measurableSet_lt h1.measurable h2.measurable
  have hA1m : MeasurableSet {x : Fin (m + 1) → ℝ | c ≤ |x 0|} :=
    measurableSet_le measurable_const (continuous_abs.comp (continuous_apply 0)).measurable
  have hA2m : MeasurableSet {x : Fin (m + 1) → ℝ | ∑ j : Fin m, x j.succ ^ 2 < m * c ^ 2} := by
    have h1 : Continuous fun x : Fin (m + 1) → ℝ => ∑ j : Fin m, x j.succ ^ 2 := by fun_prop
    exact measurableSet_lt h1.measurable measurable_const
  have hpt : ∀ x : Fin (m + 1) → ℝ,
      Set.indicator {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < ((m : ℝ) + 1) * x 0 ^ 2}
          (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))) x
        ≤ Set.indicator {x : Fin (m + 1) → ℝ | c ≤ |x 0|}
            (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))) x
          + Set.indicator {x : Fin (m + 1) → ℝ | ∑ j : Fin m, x j.succ ^ 2 < m * c ^ 2}
            (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))) x := by
    intro x
    by_cases hx : x ∈ {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < ((m : ℝ) + 1) * x 0 ^ 2}
    · rw [Set.indicator_of_mem hx]
      have hsum : ∑ i, x i ^ 2 = x 0 ^ 2 + ∑ j : Fin m, x j.succ ^ 2 := Fin.sum_univ_succ _
      have hS : ∑ j : Fin m, x j.succ ^ 2 < (m : ℝ) * x 0 ^ 2 := by
        have := hx
        simp only [Set.mem_setOf_eq, hsum] at this
        nlinarith [this]
      by_cases h1 : c ≤ |x 0|
      · exact le_add_right (Set.indicator_of_mem
          (show x ∈ {x : Fin (m + 1) → ℝ | c ≤ |x 0|} from h1)
          (fun x : Fin (m + 1) → ℝ => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2)))).ge
      · refine le_add_left (Set.indicator_of_mem (a := x) (f := fun x : Fin (m + 1) → ℝ =>
          ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))) (s := {x : Fin (m + 1) → ℝ |
            ∑ j : Fin m, x j.succ ^ 2 < m * c ^ 2}) ?_).ge
        have hlt : x 0 ^ 2 < c ^ 2 := by
          have habs : |x 0| < c := lt_of_not_ge h1
          have h0 : (0 : ℝ) ≤ |x 0| := abs_nonneg _
          nlinarith [sq_abs (x 0)]
        show ∑ j : Fin m, x j.succ ^ 2 < (m : ℝ) * c ^ 2
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith [hS, hlt, hm]
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have hmeas1 : Measurable (Set.indicator {x : Fin (m + 1) → ℝ | c ≤ |x 0|}
      (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2)))) := by
    refine Measurable.indicator ?_ hA1m
    fun_prop
  rw [← lintegral_indicator hCm]
  refine le_trans (lintegral_mono hpt) ?_
  rw [lintegral_add_left hmeas1]
  exact add_le_add (le_of_eq (lintegral_gauss_slab m c)) (lintegral_gauss_shell_le m hlam)

end Gaussian

/-! ## From the cone of `Fin n → ℝ` back to the sphere -/

section Transfer

variable {n : ℕ}

/-- The open cone over the cap, in the sphere's own space. -/
theorem smul_image_cap_eq [NeZero n] :
    (Set.Ioo (0 : ℝ) 1) • ((↑) '' {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ⟪(θ : EuclideanSpace ℝ (Fin n)),
          EuclideanSpace.single (0 : Fin n) (1 : ℝ)⟫ ∈ {t : ℝ | 1 < (n : ℝ) * t ^ 2}})
      = {x : EuclideanSpace ℝ (Fin n) | ‖x‖ < 1 ∧
          ‖x‖ ^ 2 < (n : ℝ) * ⟪x, EuclideanSpace.single (0 : Fin n) (1 : ℝ)⟫ ^ 2} := by
  ext x
  simp only [Set.mem_smul, Set.mem_image, Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨r, ⟨hr0, hr1⟩, y, ⟨θ, hθ, rfl⟩, rfl⟩
    have hθ1 : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.1 θ.2
    have hnorm : ‖r • (θ : EuclideanSpace ℝ (Fin n))‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hθ1, mul_one]
    refine ⟨by rw [hnorm]; exact hr1, ?_⟩
    rw [hnorm, real_inner_smul_left]
    have h1 : (1 : ℝ) < (n : ℝ) * ⟪(θ : EuclideanSpace ℝ (Fin n)),
        EuclideanSpace.single (0 : Fin n) (1 : ℝ)⟫ ^ 2 := hθ
    have hr2 : (0 : ℝ) < r ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_right h1 hr2]
  · rintro ⟨hx1, hx2⟩
    have hxne : x ≠ 0 := by
      intro h
      rw [h] at hx2
      simp at hx2
    have hrpos : 0 < ‖x‖ := norm_pos_iff.2 hxne
    have hunit : ‖‖x‖⁻¹ • x‖ = 1 := norm_smul_inv_norm hxne
    refine ⟨‖x‖, ⟨hrpos, hx1⟩, ‖x‖⁻¹ • x, ⟨⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.2 hunit⟩, ?_, rfl⟩,
      by rw [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]⟩
    show (1 : ℝ) < (n : ℝ) * ⟪‖x‖⁻¹ • x, EuclideanSpace.single (0 : Fin n) (1 : ℝ)⟫ ^ 2
    rw [real_inner_smul_left]
    have hinv2 : (‖x‖⁻¹) ^ 2 * ‖x‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hrpos.ne', one_pow]
    have hpos2 : (0 : ℝ) < (‖x‖⁻¹) ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left hx2 hpos2, hinv2]

/-- The cone and the ball of `EuclideanSpace ℝ (Fin n)`, pulled back to `Fin n → ℝ`. -/
theorem preimage_ofLp_cone [NeZero n] :
    ((WithLp.ofLp) ⁻¹' ({x : Fin n → ℝ | ∑ i, x i ^ 2 < (n : ℝ) * x 0 ^ 2}
        ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1}) : Set (EuclideanSpace ℝ (Fin n)))
      = {x : EuclideanSpace ℝ (Fin n) | ‖x‖ < 1 ∧
          ‖x‖ ^ 2 < (n : ℝ) * ⟪x, EuclideanSpace.single (0 : Fin n) (1 : ℝ)⟫ ^ 2} := by
  ext x
  have hnorm : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
  have hinner : ⟪x, EuclideanSpace.single (0 : Fin n) (1 : ℝ)⟫ = x 0 := by
    rw [EuclideanSpace.inner_single_right]
    simp
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, hinner]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by rw [hnorm]; exact h1⟩
    have : ‖x‖ ^ 2 < 1 := by rw [hnorm]; exact h2
    nlinarith [norm_nonneg x, this]
  · rintro ⟨h1, h2⟩
    rw [hnorm] at h2
    refine ⟨h2, ?_⟩
    rw [← hnorm]
    nlinarith [norm_nonneg x, h1]

/-- **The cap of the sphere is bounded by the trace of the cone on the unit ball.** -/
theorem toSphere_cap_le_of_volume_le [NeZero n] {q : ℝ}
    (hvol : volume ({x : Fin n → ℝ | ∑ i, x i ^ 2 < (n : ℝ) * x 0 ^ 2}
        ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1})
      ≤ ENNReal.ofReal q * volume {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1}) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
        {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          ⟪(θ : EuclideanSpace ℝ (Fin n)),
            EuclideanSpace.single (0 : Fin n) (1 : ℝ)⟫ ∈ {t : ℝ | 1 < (n : ℝ) * t ^ 2}}
      ≤ ENNReal.ofReal q * sphereArea n := by
  have hBm : MeasurableSet {t : ℝ | 1 < (n : ℝ) * t ^ 2} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hS : MeasurableSet {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      ⟪(θ : EuclideanSpace ℝ (Fin n)),
        EuclideanSpace.single (0 : Fin n) (1 : ℝ)⟫ ∈ {t : ℝ | 1 < (n : ℝ) * t ^ 2}} :=
    measurableSet_sphere_setOf_inner hBm
  have hCm : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ^ 2 < (n : ℝ) * x 0 ^ 2} := by
    have h1 : Continuous fun x : Fin n → ℝ => ∑ i, x i ^ 2 := by fun_prop
    have h2 : Continuous fun x : Fin n → ℝ => (n : ℝ) * x 0 ^ 2 := by fun_prop
    exact measurableSet_lt h1.measurable h2.measurable
  have hBallm : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1} := measurableSet_sqLt n 1
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1
      = (WithLp.ofLp) ⁻¹' {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1} := by
    ext x
    have hnorm : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
    simp only [Metric.mem_ball, dist_zero_right, Set.mem_preimage, Set.mem_setOf_eq, ← hnorm]
    constructor
    · intro h; nlinarith [norm_nonneg x]
    · intro h; nlinarith [norm_nonneg x]
  rw [Measure.toSphere_apply' _ hS, sphereArea_eq, finrank_euclideanSpace_fin, smul_image_cap_eq,
    ← preimage_ofLp_cone, hball,
    (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage (hCm.inter hBallm).nullMeasurableSet,
    (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hBallm.nullMeasurableSet]
  calc (n : ℝ≥0∞) * volume ({x : Fin n → ℝ | ∑ i, x i ^ 2 < (n : ℝ) * x 0 ^ 2}
        ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1})
      ≤ (n : ℝ≥0∞) * (ENNReal.ofReal q * volume {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1}) := by
        exact mul_le_mul_right hvol _
    _ = ENNReal.ofReal q * ((n : ℝ≥0∞) * volume {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1}) := by
        rw [← mul_assoc, ← mul_assoc, mul_comm (n : ℝ≥0∞)]

end Transfer

/-! ## The one-dimensional numerics -/

section Numerics

/-- **The degree-10 Taylor polynomial underestimates the Gaussian** on `|t| ≤ √2`.  This is
`Real.exp_bound` at order five, in the variable `u = t²/2`; the fourth-order term is kept
because the fifth-order remainder alone is too coarse for the budget below. -/
theorem poly_le_gauss {t : ℝ} (ht : t ^ 2 ≤ 2) :
    1 - t ^ 2 / 2 + t ^ 4 / 8 - t ^ 6 / 48 + t ^ 8 / 384 - t ^ 10 / 3200
      ≤ Real.exp (-(t ^ 2) / 2) := by
  set x : ℝ := -(t ^ 2) / 2 with hx
  have hx1 : |x| ≤ 1 := by
    rw [hx, abs_le]
    constructor <;> nlinarith [sq_nonneg t]
  have h := Real.exp_bound hx1 (n := 5) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 5, x ^ m / (m.factorial : ℝ)
      = 1 - t ^ 2 / 2 + t ^ 4 / 8 - t ^ 6 / 48 + t ^ 8 / 384 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    rw [hx]
    norm_num
    ring
  have habs : |x| ^ 5 * ((5 : ℕ).succ / ((5 : ℕ).factorial * (5 : ℕ)) : ℝ)
      = t ^ 10 / 3200 := by
    have : |x| = t ^ 2 / 2 := by
      rw [hx, abs_div, abs_neg, abs_of_nonneg (sq_nonneg t)]
      norm_num
    rw [this]
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    norm_num
    ring
  rw [hsum, habs] at h
  have := abs_le.1 h
  linarith [this.1]

/-- The integral of that polynomial. -/
theorem integral_poly (c : ℝ) :
    (∫ t in (-c)..c, (1 - t ^ 2 / 2 + t ^ 4 / 8 - t ^ 6 / 48 + t ^ 8 / 384 - t ^ 10 / 3200))
      = 2 * (c - c ^ 3 / 6 + c ^ 5 / 40 - c ^ 7 / 336 + c ^ 9 / 3456 - c ^ 11 / 35200) := by
  have hderiv : ∀ t ∈ Set.uIcc (-c) c,
      HasDerivAt (fun s : ℝ => s - s ^ 3 / 6 + s ^ 5 / 40 - s ^ 7 / 336 + s ^ 9 / 3456
          - s ^ 11 / 35200)
        (1 - t ^ 2 / 2 + t ^ 4 / 8 - t ^ 6 / 48 + t ^ 8 / 384 - t ^ 10 / 3200) t := by
    intro t _
    refine HasDerivAt.congr_deriv (((((( hasDerivAt_id t).sub
      ((hasDerivAt_pow 3 t).div_const 6)).add
      ((hasDerivAt_pow 5 t).div_const 40)).sub ((hasDerivAt_pow 7 t).div_const 336)).add
      ((hasDerivAt_pow 9 t).div_const 3456)).sub ((hasDerivAt_pow 11 t).div_const 35200)) ?_
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- **The Gaussian tail beyond `c = 23/25`.**  This is the estimate that earns the constant:
the threshold is at the root-mean-square value, where every moment bound is trivial, so the
head has to be integrated honestly. -/
theorem gauss_tail_le :
    (∫ t : ℝ, Set.indicator {t : ℝ | (23 / 25 : ℝ) ≤ |t|}
        (fun t => Real.exp (-(t ^ 2) / 2)) t)
      ≤ Real.sqrt (2 * Real.pi) - 1.6103 := by
  have hSm : MeasurableSet {t : ℝ | (23 / 25 : ℝ) ≤ |t|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hsplit : (∫ t in {t : ℝ | (23 / 25 : ℝ) ≤ |t|}, Real.exp (-(t ^ 2) / 2))
      + (∫ t in {t : ℝ | (23 / 25 : ℝ) ≤ |t|}ᶜ, Real.exp (-(t ^ 2) / 2))
      = Real.sqrt (2 * Real.pi) := by
    rw [integral_add_compl hSm integrable_gauss_half, integral_gauss_half]
  have hcompl : {t : ℝ | (23 / 25 : ℝ) ≤ |t|}ᶜ = Set.Ioo (-(23 / 25 : ℝ)) (23 / 25) := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Set.mem_Ioo, abs_lt]
  have hIoo : (∫ t in Set.Ioo (-(23 / 25 : ℝ)) (23 / 25), Real.exp (-(t ^ 2) / 2))
      = ∫ t in (-(23 / 25 : ℝ))..(23 / 25), Real.exp (-(t ^ 2) / 2) := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  have hmono : (2 : ℝ) * ((23 / 25 : ℝ) - (23 / 25 : ℝ) ^ 3 / 6 + (23 / 25 : ℝ) ^ 5 / 40
        - (23 / 25 : ℝ) ^ 7 / 336 + (23 / 25 : ℝ) ^ 9 / 3456 - (23 / 25 : ℝ) ^ 11 / 35200)
      ≤ ∫ t in (-(23 / 25 : ℝ))..(23 / 25), Real.exp (-(t ^ 2) / 2) := by
    rw [← integral_poly (23 / 25 : ℝ)]
    refine intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; fun_prop)
      integrable_gauss_half.intervalIntegrable fun t ht => ?_
    refine poly_le_gauss ?_
    have h1 : -(23 / 25 : ℝ) ≤ t := ht.1
    have h2 : t ≤ (23 / 25 : ℝ) := ht.2
    nlinarith
  rw [integral_indicator hSm]
  have hpoly : (1.6103 : ℝ)
      ≤ 2 * ((23 / 25 : ℝ) - (23 / 25 : ℝ) ^ 3 / 6 + (23 / 25 : ℝ) ^ 5 / 40
        - (23 / 25 : ℝ) ^ 7 / 336 + (23 / 25 : ℝ) ^ 9 / 3456 - (23 / 25 : ℝ) ^ 11 / 35200) := by
    norm_num
  rw [hcompl, hIoo] at hsplit
  linarith

theorem sqrt_two_pi_le : Real.sqrt (2 * Real.pi) ≤ 2.50663 := by
  have h : 2 * Real.pi ≤ (2.50663 : ℝ) ^ 2 := by nlinarith [Real.pi_lt_d6]
  calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt ((2.50663 : ℝ) ^ 2) := Real.sqrt_le_sqrt h
    _ = 2.50663 := Real.sqrt_sq (by norm_num)

theorem sqrt_two_pi_pos : 0 < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.2 (by positivity)

/-- The exponential moment factor at `λ = 9/100`, `c = 23/25`. -/
theorem exp_lam_le : Real.exp ((9 / 100 : ℝ) * (23 / 25 : ℝ) ^ 2) ≤ 1.0792 := by
  have hval : (9 / 100 : ℝ) * (23 / 25 : ℝ) ^ 2 = 4761 / 62500 := by norm_num
  rw [hval]
  have hx1 : |(4761 / 62500 : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4761 / 62500)]
    norm_num
  have h := Real.exp_bound hx1 (n := 4) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 4, (4761 / 62500 : ℝ) ^ m / (m.factorial : ℝ)
      = 1 + (4761 / 62500 : ℝ) + (4761 / 62500 : ℝ) ^ 2 / 2 + (4761 / 62500 : ℝ) ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  rw [hsum, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4761 / 62500)] at h
  have h2 := (abs_le.1 h).2
  norm_num at h2
  linarith

/-- **The per-coordinate Chernoff factor is a strict contraction.** -/
theorem chernoff_factor_le :
    Real.exp ((9 / 100 : ℝ) * (23 / 25 : ℝ) ^ 2)
        * Real.sqrt (Real.pi / ((9 / 100 : ℝ) + 1 / 2))
      ≤ 0.994 * Real.sqrt (2 * Real.pi) := by
  have hsplit : Real.sqrt (2 * Real.pi)
      = Real.sqrt 1.18 * Real.sqrt (Real.pi / ((9 / 100 : ℝ) + 1 / 2)) := by
    rw [← Real.sqrt_mul (by norm_num)]
    congr 1
    rw [show (1.18 : ℝ) = 118 / 100 by norm_num,
      show (9 / 100 : ℝ) + 1 / 2 = 59 / 100 by norm_num]
    ring
  have hroot : (1.08627 : ℝ) ≤ Real.sqrt 1.18 := by
    calc (1.08627 : ℝ) = Real.sqrt ((1.08627 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 1.18 := Real.sqrt_le_sqrt (by norm_num)
  have hS : 0 ≤ Real.sqrt (Real.pi / ((9 / 100 : ℝ) + 1 / 2)) := Real.sqrt_nonneg _
  rw [hsplit]
  have hkey : Real.exp ((9 / 100 : ℝ) * (23 / 25 : ℝ) ^ 2) ≤ 0.994 * Real.sqrt 1.18 := by
    have := exp_lam_le
    nlinarith [hroot]
  calc Real.exp ((9 / 100 : ℝ) * (23 / 25 : ℝ) ^ 2)
        * Real.sqrt (Real.pi / ((9 / 100 : ℝ) + 1 / 2))
      ≤ (0.994 * Real.sqrt 1.18) * Real.sqrt (Real.pi / ((9 / 100 : ℝ) + 1 / 2)) := by
        exact mul_le_mul_of_nonneg_right hkey hS
    _ = 0.994 * (Real.sqrt 1.18 * Real.sqrt (Real.pi / ((9 / 100 : ℝ) + 1 / 2))) := by ring

/-- `0.994^m` is small once `m ≥ 1099`. -/
theorem pow_contraction_le {m : ℕ} (hm : 1099 ≤ m) : (0.994 : ℝ) ^ m ≤ 0.0022 := by
  have h157 : (0.994 : ℝ) ^ 157 ≤ 0.389 := by
    rw [show (0.994 : ℝ) = 497 / 500 by norm_num, div_pow,
      div_le_iff₀ (by positivity : (0 : ℝ) < 500 ^ 157)]
    norm_num
  calc (0.994 : ℝ) ^ m ≤ (0.994 : ℝ) ^ 1099 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    _ = ((0.994 : ℝ) ^ 157) ^ 7 := by rw [← pow_mul]
    _ ≤ (0.389 : ℝ) ^ 7 := by
        exact pow_le_pow_left₀ (by positivity) h157 7
    _ ≤ 0.0022 := by norm_num

end Numerics

section CapSlice

open Real
open scoped Real

/-! ## The exact cross-section, and the cap bound from dimension 21

⚠ **This section supersedes the Gaussian union bound above.**  That route proves the same
`9/25` only from `n ≥ 1100`, and §2 of `lean/PLAN-SPHERECAP.md` shows the threshold cannot be
lowered by retuning it: at `n = 21` the best `(c, λ)` gives `≈ 0.57` against a target of
`0.36`.  The obstruction is that the union bound never sees the *shape* of the cross-section,
only a tail and a Chernoff factor.

What is done here instead is to compute the cross-section exactly.  Slicing the unit ball of
`Fin (m+1) → ℝ` along coordinate `0` (`volume_slice`, a `Fubini` step through
`MeasureTheory.volume_preserving_piFinSuccAbove`), the slice at height `s` is an `m`-ball of
radius `√(1-s²)` and the cone's slice is an `m`-ball of radius `√(m s²)`, so the whole ratio
collapses to a one-dimensional integral.  Three elementary estimates finish it:

* **Bernoulli** `(1-s²)^{m/2} ≥ 1 - (m/2)s²` for the numerator (`chord_ge`);
* the **exact** cone term `((m/(m+1))^{m/2})·(m+1)⁻¹` (`integral_spike`), bounded by
  `e^{-1/2}·e^{1/42} ≤ 0.6215` (`coneFactor_le`);
* the **Wallis pairing** `k·P_k·P_{k-1} = 2π` (`P_pairing`) together with `P` antitone, giving
  `P_{m+1}² ≤ 2π/(m+1)` (`P_sq_le`) for the denominator — no Gamma function, no Beta
  distribution, and in particular **not** the `Γ→Β` bridge that `PLAN-SPHERECAP.md` §3 scopes
  as "the work".  Mathlib's `integral_sin_pow` recursion is the whole input.

The chain yields `cap ≤ 9/25` from `n ≥ 15`; it is stated at `n ≥ 21` — TTC's own floor —
because the margin at 15 is `0.0015` before rational rounding and the rounding here spends
about `0.008` of it.  The true cap fraction is `0.3293` at `n = 21`, so the bound is honest
but not sharp; the statement itself is true from `n = 6` on and false for `n ≤ 4`, so *some*
dimension hypothesis is mandatory. -/

/-! ## §1  The Wallis integrals -/

noncomputable def P (k : ℕ) : ℝ := ∫ x in (0:ℝ)..π, Real.sin x ^ k

theorem P_zero : P 0 = π := by simp [P]

theorem P_one : P 1 = 2 := by simp [P, integral_sin]; norm_num

theorem P_succ_succ (k : ℕ) : P (k + 2) = ((k : ℝ) + 1) / ((k : ℝ) + 2) * P k := by
  unfold P; rw [integral_sin_pow]; simp

theorem P_pairing (k : ℕ) : ((k : ℝ) + 1) * P (k + 1) * P k = 2 * π := by
  induction k with
  | zero => rw [P_zero, P_one]; push_cast; ring
  | succ j ih =>
      have h := P_succ_succ j
      push_cast at *
      rw [show j + 1 + 1 = j + 2 from rfl, h]
      field_simp
      nlinarith [ih]

theorem P_pos (k : ℕ) : 0 < P k := integral_sin_pow_pos k

theorem P_anti : Antitone P := integral_sin_pow_antitone

theorem P_sq_le (m : ℕ) : P (m + 1) ^ 2 ≤ 2 * π / ((m : ℝ) + 1) := by
  have hp := P_pairing m
  have hle : P (m + 1) ≤ P m := P_anti (Nat.le_succ m)
  have hpos := P_pos (m + 1)
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hm]
  have hstep : P (m + 1) * P (m + 1) ≤ P (m + 1) * P m :=
    mul_le_mul_of_nonneg_left hle hpos.le
  nlinarith [hstep, hp, hm]

/-! ## §2  The two profile functions -/

noncomputable def chord (m : ℕ) (s : ℝ) : ℝ := (Real.sqrt (1 - s ^ 2)) ^ m
noncomputable def spike (m : ℕ) (s : ℝ) : ℝ := (Real.sqrt ((m : ℝ) * s ^ 2)) ^ m
noncomputable def s0 (m : ℕ) : ℝ := Real.sqrt (1 / ((m : ℝ) + 1))

theorem chord_nonneg (m : ℕ) (s : ℝ) : 0 ≤ chord m s := by unfold chord; positivity
theorem spike_nonneg (m : ℕ) (s : ℝ) : 0 ≤ spike m s := by unfold spike; positivity
theorem continuous_chord (m : ℕ) : Continuous (chord m) := by unfold chord; fun_prop
theorem continuous_spike (m : ℕ) : Continuous (spike m) := by unfold spike; fun_prop

theorem s0_pos (m : ℕ) : 0 < s0 m := Real.sqrt_pos.2 (by positivity)
theorem s0_sq (m : ℕ) : (s0 m) ^ 2 = 1 / ((m : ℝ) + 1) := Real.sq_sqrt (by positivity)

theorem s0_le_one (m : ℕ) : s0 m ≤ 1 := by
  have h := s0_sq m
  have hle : (1:ℝ) / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  nlinarith [s0_pos m, h, hle]

theorem chord_cos (m : ℕ) {x : ℝ} (hx : x ∈ uIcc (0:ℝ) π) :
    chord m (Real.cos x) = Real.sin x ^ m := by
  rw [uIcc_of_le Real.pi_pos.le] at hx
  have hs : 0 ≤ Real.sin x := Real.sin_nonneg_of_mem_Icc hx
  unfold chord
  rw [show (1 : ℝ) - Real.cos x ^ 2 = Real.sin x ^ 2 by
    have := Real.sin_sq_add_cos_sq x; linarith, Real.sqrt_sq hs]

/-- **`∫_{-1}^{1}(√(1-s²))^m ds = ∫_0^π sinᵐ⁺¹`**, by `s = cos θ`. -/
theorem integral_chord (m : ℕ) : (∫ s in (-1:ℝ)..1, chord m s) = P (m + 1) := by
  have hderiv : ∀ x ∈ uIcc (0:ℝ) π, HasDerivAt Real.cos (-Real.sin x) x :=
    fun x _ => Real.hasDerivAt_cos x
  have hcont : ContinuousOn (fun x : ℝ => -Real.sin x) (uIcc (0:ℝ) π) := by fun_prop
  have hsub := intervalIntegral.integral_comp_smul_deriv hderiv hcont (continuous_chord m)
  rw [Real.cos_zero, Real.cos_pi] at hsub
  have hL : (∫ x in (0:ℝ)..π, (-Real.sin x) • (chord m ∘ Real.cos) x)
      = ∫ x in (0:ℝ)..π, -(Real.sin x ^ (m + 1)) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    simp only [Function.comp_apply, smul_eq_mul]
    rw [chord_cos m hx]; ring
  rw [hL, intervalIntegral.integral_neg] at hsub
  have hflip : (∫ x in (1:ℝ)..(-1), chord m x) = -∫ x in (-1:ℝ)..1, chord m x :=
    intervalIntegral.integral_symm (-1) 1
  rw [hflip] at hsub
  have hP : P (m + 1) = ∫ x in (0:ℝ)..π, Real.sin x ^ (m + 1) := rfl
  rw [hP]; linarith

/-! ## §3  Slicing the ball -/

noncomputable def unitVol (m : ℕ) : ℝ≥0∞ := volume {y : Fin m → ℝ | ∑ j, y j ^ 2 < 1}

theorem unitVol_ne_top (m : ℕ) : unitVol m ≠ ⊤ := by
  have hsub : {y : Fin m → ℝ | ∑ j, y j ^ 2 < 1}
      ⊆ Set.univ.pi fun _ : Fin m => Set.Ioo (-1 : ℝ) 1 := by
    intro y hy j _
    simp only [Set.mem_setOf_eq] at hy
    have hj : y j ^ 2 ≤ ∑ i, y i ^ 2 :=
      Finset.single_le_sum (f := fun i => y i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have h1 : y j ^ 2 < 1 := lt_of_le_of_lt hj hy
    constructor <;> nlinarith
  refine ne_of_lt (lt_of_le_of_lt (measure_mono hsub) ?_)
  rw [volume_pi_pi]
  simp only [Real.volume_Ioo, sub_neg_eq_add, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

theorem volume_sqLt_eq {m : ℕ} (hm : m ≠ 0) {R : ℝ} (hR : 0 ≤ R) :
    volume {x : Fin m → ℝ | ∑ i, x i ^ 2 < R ^ 2}
      = ENNReal.ofReal (R ^ m) * unitVol m := by
  have h := volume_cone_inter_sqLt (C := Set.univ) (n := m) hm
    (fun r hr => smul_univ_eq m hr) hR
  simpa [unitVol] using h

theorem volume_sqLt_sqrt {m : ℕ} (hm : m ≠ 0) (c : ℝ) :
    volume {y : Fin m → ℝ | ∑ j, y j ^ 2 < c}
      = ENNReal.ofReal ((Real.sqrt c) ^ m) * unitVol m := by
  rcases le_or_gt 0 c with hc | hc
  · have hsq : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc
    rw [← hsq, volume_sqLt_eq hm (Real.sqrt_nonneg c), hsq]
  · have hempty : {y : Fin m → ℝ | ∑ j, y j ^ 2 < c} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans hc.le (Finset.sum_nonneg fun j _ => sq_nonneg (y j))
    rw [hempty, measure_empty, Real.sqrt_eq_zero_of_nonpos hc.le, zero_pow hm,
      ENNReal.ofReal_zero, zero_mul]

theorem sqrt_min_pow (m : ℕ) (a b : ℝ) :
    (Real.sqrt (min a b)) ^ m = min ((Real.sqrt a) ^ m) ((Real.sqrt b) ^ m) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (pow_le_pow_left₀ (Real.sqrt_nonneg a)
      (Real.sqrt_le_sqrt h) m)]
  · rw [min_eq_right h, min_eq_right (pow_le_pow_left₀ (Real.sqrt_nonneg b)
      (Real.sqrt_le_sqrt h) m)]

theorem sum_sq_cons {m : ℕ} (s : ℝ) (y : Fin m → ℝ) :
    ∑ i, (Fin.cons s y : Fin (m + 1) → ℝ) i ^ 2 = s ^ 2 + ∑ j, y j ^ 2 := by
  rw [Fin.sum_univ_succ]; simp

/-- **Lebesgue measure on `Fin (m+1) → ℝ`, sliced along coordinate `0`.** -/
theorem volume_slice {m : ℕ} {S : Set (Fin (m + 1) → ℝ)} (hS : MeasurableSet S) :
    volume S = ∫⁻ s : ℝ, volume {y : Fin m → ℝ | Fin.cons s y ∈ S} := by
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 with he
  set T : Set (ℝ × (Fin m → ℝ)) := e.symm ⁻¹' S with hT
  have hTm : MeasurableSet T := e.symm.measurable hS
  have hpre : e ⁻¹' T = S := by rw [hT, ← Set.preimage_comp]; simp
  have h1 : volume S = volume T := by
    rw [← hpre, hmp.measure_preimage hTm.nullMeasurableSet]
  rw [h1, MeasureTheory.Measure.volume_eq_prod, Measure.prod_apply hTm]
  congr 1
  funext s
  congr 1
  ext y
  simp [hT, he, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv_zero, Fin.consEquiv]

theorem sliceBallVol {m : ℕ} (hm : m ≠ 0) :
    volume {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < 1}
      = (∫⁻ s : ℝ, ENNReal.ofReal (chord m s)) * unitVol m := by
  rw [volume_slice (measurableSet_sqLt (m + 1) 1),
    ← lintegral_mul_const' _ _ (unitVol_ne_top m)]
  congr 1
  funext s
  have hset : {y : Fin m → ℝ | (Fin.cons s y : Fin (m+1) → ℝ) ∈
      {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < 1}}
      = {y : Fin m → ℝ | ∑ j, y j ^ 2 < 1 - s ^ 2} := by
    ext y; simp only [Set.mem_setOf_eq, sum_sq_cons]; constructor <;> intro h <;> linarith
  rw [hset, volume_sqLt_sqrt hm]
  rfl

theorem sliceConeVol {m : ℕ} (hm : m ≠ 0) :
    volume ({x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < ((m : ℝ) + 1) * x 0 ^ 2}
        ∩ {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < 1})
      = (∫⁻ s : ℝ, ENNReal.ofReal (min (spike m s) (chord m s))) * unitVol m := by
  have hms : MeasurableSet ({x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < ((m : ℝ) + 1) * x 0 ^ 2}
      ∩ {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < 1}) := by
    refine MeasurableSet.inter ?_ (measurableSet_sqLt (m + 1) 1)
    have h1 : Continuous fun x : Fin (m + 1) → ℝ => ∑ i, x i ^ 2 := by fun_prop
    have h2 : Continuous fun x : Fin (m + 1) → ℝ => ((m : ℝ) + 1) * x 0 ^ 2 := by fun_prop
    exact measurableSet_lt h1.measurable h2.measurable
  rw [volume_slice hms, ← lintegral_mul_const' _ _ (unitVol_ne_top m)]
  congr 1
  funext s
  have hset : {y : Fin m → ℝ | (Fin.cons s y : Fin (m+1) → ℝ) ∈
      ({x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < ((m : ℝ) + 1) * x 0 ^ 2}
        ∩ {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < 1})}
      = {y : Fin m → ℝ | ∑ j, y j ^ 2 < min ((m : ℝ) * s ^ 2) (1 - s ^ 2)} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, sum_sq_cons, Fin.cons_zero, lt_min_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by linarith⟩
  rw [hset, volume_sqLt_sqrt hm, sqrt_min_pow]
  rfl


/-! ## §4  Integrability and the passage to real integrals -/

theorem chord_eq_zero {m : ℕ} (hm : m ≠ 0) {s : ℝ} (hs : s ∉ Set.Ioc (-1 : ℝ) 1) :
    chord m s = 0 := by
  have h : 1 - s ^ 2 ≤ 0 := by
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
    rcases hs with h | h
    · nlinarith
    · nlinarith
  unfold chord
  rw [Real.sqrt_eq_zero_of_nonpos h, zero_pow hm]

theorem integrable_chord {m : ℕ} (hm : m ≠ 0) : Integrable (chord m) := by
  have hsupp : Function.support (chord m) ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro s hs
    by_contra hc
    exact hs (chord_eq_zero hm (fun h => hc ⟨le_of_lt h.1, h.2⟩))
  exact (continuous_chord m).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)

theorem integrable_min {m : ℕ} (hm : m ≠ 0) :
    Integrable (fun s => min (spike m s) (chord m s)) := by
  refine Integrable.mono (integrable_chord hm)
    (((continuous_spike m).min (continuous_chord m)).aestronglyMeasurable) ?_
  filter_upwards with s
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (le_min (spike_nonneg m s) (chord_nonneg m s)),
    abs_of_nonneg (chord_nonneg m s)]
  exact min_le_right _ _

theorem lintegral_chord {m : ℕ} (hm : m ≠ 0) :
    (∫⁻ s : ℝ, ENNReal.ofReal (chord m s)) = ENNReal.ofReal (∫ s in (-1 : ℝ)..1, chord m s) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs => chord_eq_zero hm hs),
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_chord hm)
      (Filter.Eventually.of_forall (chord_nonneg m))]

theorem lintegral_min {m : ℕ} (hm : m ≠ 0) :
    (∫⁻ s : ℝ, ENNReal.ofReal (min (spike m s) (chord m s)))
      = ENNReal.ofReal (∫ s : ℝ, min (spike m s) (chord m s)) :=
  (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_min hm)
    (Filter.Eventually.of_forall (fun s => le_min (spike_nonneg m s) (chord_nonneg m s)))).symm

/-! ## §5  Where the cone sits inside the ball -/

theorem spike_le_chord_iff {m : ℕ} (hm : m ≠ 0) (s : ℝ) :
    spike m s ≤ chord m s ↔ ((m : ℝ) + 1) * s ^ 2 ≤ 1 := by
  unfold spike chord
  rw [pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hm]
  rcases le_or_gt 0 (1 - s ^ 2) with hc | hc
  · rw [Real.sqrt_le_sqrt_iff hc]
    constructor <;> intro h <;> nlinarith
  · rw [Real.sqrt_eq_zero_of_nonpos hc.le]
    have hs1 : 1 < s ^ 2 := by linarith
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
    constructor
    · intro h
      have h0 : Real.sqrt ((m : ℝ) * s ^ 2) = 0 := le_antisymm h (Real.sqrt_nonneg _)
      have h2 : (m : ℝ) * s ^ 2 ≤ 0 := by
        by_contra hpos
        exact absurd h0 (ne_of_gt (Real.sqrt_pos.2 (lt_of_not_ge hpos)))
      nlinarith
    · intro h; nlinarith

theorem chord_sub_min {m : ℕ} (hm : m ≠ 0) (s : ℝ) :
    chord m s - min (spike m s) (chord m s)
      = Set.indicator {t : ℝ | ((m : ℝ) + 1) * t ^ 2 ≤ 1}
          (fun t => chord m t - spike m t) s := by
  by_cases h : s ∈ {t : ℝ | ((m : ℝ) + 1) * t ^ 2 ≤ 1}
  · rw [Set.indicator_of_mem h, min_eq_left ((spike_le_chord_iff hm s).2 h)]
  · rw [Set.indicator_of_notMem h,
      min_eq_right (le_of_not_ge (fun hle => h ((spike_le_chord_iff hm s).1 hle)))]
    ring

theorem crossover_eq (m : ℕ) :
    {t : ℝ | ((m : ℝ) + 1) * t ^ 2 ≤ 1} = Set.Icc (-(s0 m)) (s0 m) := by
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  rw [← abs_le, ← Real.sqrt_sq_eq_abs]
  constructor
  · intro h
    have h2 : t ^ 2 ≤ 1 / ((m : ℝ) + 1) := by rw [le_div_iff₀ hden]; linarith
    calc Real.sqrt (t ^ 2) ≤ Real.sqrt (1 / ((m : ℝ) + 1)) := Real.sqrt_le_sqrt h2
      _ = s0 m := rfl
  · intro h
    have h2 : t ^ 2 ≤ 1 / ((m : ℝ) + 1) := by
      nlinarith [Real.sq_sqrt (sq_nonneg t), s0_sq m,
        pow_le_pow_left₀ (Real.sqrt_nonneg (t ^ 2)) h 2]
    rw [le_div_iff₀ hden] at h2; linarith

/-! ## §6  The two integral estimates -/

theorem chord_ge {m : ℕ} (hm : 2 ≤ m) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    1 - (m : ℝ) / 2 * s ^ 2 ≤ chord m s := by
  have hu : (0 : ℝ) ≤ 1 - s ^ 2 := by linarith
  have hrw : chord m s = (1 - s ^ 2) ^ ((m : ℝ) / 2) := by
    unfold chord
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1 - s ^ 2) ^ ((1 : ℝ) / 2)) m,
      ← Real.rpow_mul hu]
    ring_nf
  rw [hrw]
  have hp : (1 : ℝ) ≤ (m : ℝ) / 2 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hb := one_add_mul_self_le_rpow_one_add (s := -(s ^ 2)) (by nlinarith) hp
  have he : (1 : ℝ) + -(s ^ 2) = 1 - s ^ 2 := by ring
  rw [he] at hb
  linarith [hb]

theorem integral_chord_ge {m : ℕ} (hm : 2 ≤ m) :
    2 * s0 m - (m : ℝ) / 3 * (s0 m) ^ 3 ≤ ∫ s in (-(s0 m))..(s0 m), chord m s := by
  have hle : (-(s0 m)) ≤ s0 m := by linarith [s0_pos m]
  have hpoly : (∫ s in (-(s0 m))..(s0 m), (1 - (m : ℝ) / 2 * s ^ 2))
      = 2 * s0 m - (m : ℝ) / 3 * (s0 m) ^ 3 := by
    have h1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (-(s0 m)) (s0 m) :=
      intervalIntegrable_const
    have h2 : IntervalIntegrable (fun s : ℝ => (m : ℝ) / 2 * s ^ 2) volume (-(s0 m)) (s0 m) :=
      (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul, integral_pow]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  rw [← hpoly]
  refine intervalIntegral.integral_mono_on hle
    ((continuous_const.sub (continuous_const.mul (continuous_pow 2))).intervalIntegrable _ _)
    ((continuous_chord m).intervalIntegrable _ _) (fun s hs => ?_)
  refine chord_ge hm ?_
  have h1 : s ^ 2 ≤ (s0 m) ^ 2 := by
    rcases hs with ⟨ha, hb⟩; nlinarith [s0_pos m]
  have h2 := s0_le_one m
  nlinarith [s0_pos m]

theorem integral_spike (m : ℕ) :
    (∫ s in (-(s0 m))..(s0 m), spike m s)
      = 2 * (Real.sqrt ((m : ℝ) / ((m : ℝ) + 1))) ^ m * s0 m / ((m : ℝ) + 1) := by
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hfac : ∀ s : ℝ, spike m s = (Real.sqrt (m : ℝ)) ^ m * |s| ^ m := by
    intro s
    unfold spike
    rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq_eq_abs, mul_pow]
  simp only [hfac]
  rw [intervalIntegral.integral_const_mul]
  have habs : (∫ s in (-(s0 m))..(s0 m), |s| ^ m)
      = 2 * (s0 m) ^ (m + 1) / ((m : ℝ) + 1) := by
    have hsplit : (∫ s in (-(s0 m))..(s0 m), |s| ^ m)
        = (∫ s in (-(s0 m))..(0:ℝ), |s| ^ m) + ∫ s in (0:ℝ)..(s0 m), |s| ^ m := by
      refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm <;>
        exact (continuous_abs.pow m).intervalIntegrable _ _
    have hneg : (∫ s in (-(s0 m))..(0:ℝ), |s| ^ m) = ∫ s in (0:ℝ)..(s0 m), |s| ^ m := by
      have h := intervalIntegral.integral_comp_neg (a := -(s0 m)) (b := (0:ℝ))
        (f := fun s : ℝ => |s| ^ m)
      simpa using h
    have hpos : (∫ s in (0:ℝ)..(s0 m), |s| ^ m) = ∫ s in (0:ℝ)..(s0 m), s ^ m := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [uIcc_of_le (s0_pos m).le] at hs
      rw [abs_of_nonneg hs.1]
    rw [hsplit, hneg, hpos, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero m), sub_zero]
    ring
  rw [habs]
  have hX : (Real.sqrt (m : ℝ)) ^ m * (s0 m) ^ m
      = (Real.sqrt ((m : ℝ) / ((m : ℝ) + 1))) ^ m := by
    rw [← mul_pow]
    congr 1
    unfold s0
    rw [← Real.sqrt_mul (Nat.cast_nonneg m)]
    congr 1
    field_simp
  rw [pow_succ]
  field_simp
  nlinarith [hX, s0_pos m]

/-! ## §7  The numerals -/

theorem exp_neg_half_le : Real.exp (-(1/2 : ℝ)) ≤ 0.6066 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hsq : Real.exp ((1:ℝ)/2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpos : 0 < Real.exp ((1:ℝ)/2) := Real.exp_pos _
  have hlb : (1.64853 : ℝ) < Real.exp ((1:ℝ)/2) := by nlinarith [hsq, he, hpos]
  rw [show -(1/2 : ℝ) = -((1:ℝ)/2) by ring, Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
  nlinarith [hlb]

theorem exp_inv_fortytwo_le : Real.exp ((1:ℝ)/42) ≤ 42/41 := by
  have h := Real.add_one_le_exp (-(1/42 : ℝ))
  have hpos : 0 < Real.exp (-(1/42 : ℝ)) := Real.exp_pos _
  have h41 : (41/42 : ℝ) ≤ Real.exp (-(1/42 : ℝ)) := by linarith
  rw [show ((1:ℝ)/42) = -(-(1/42 : ℝ)) by ring, Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
  nlinarith [h41]

theorem coneFactor_le {m : ℕ} (hm : 20 ≤ m) :
    (Real.sqrt ((m : ℝ) / ((m : ℝ) + 1))) ^ m ≤ 0.6215 := by
  have hm0 : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hb := Real.add_one_le_exp (-(1 / ((m : ℝ) + 1)))
  have hfrac : (m : ℝ) / ((m : ℝ) + 1) ≤ Real.exp (-(1 / ((m : ℝ) + 1))) := by
    have hr : (m : ℝ) / ((m : ℝ) + 1) = -(1 / ((m : ℝ) + 1)) + 1 := by field_simp; ring
    rw [hr]; linarith
  have hs : Real.sqrt ((m : ℝ) / ((m : ℝ) + 1)) ≤ Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) := by
    calc Real.sqrt ((m : ℝ) / ((m : ℝ) + 1))
        ≤ Real.sqrt (Real.exp (-(1 / ((m : ℝ) + 1)))) := Real.sqrt_le_sqrt hfrac
      _ = Real.exp (-(1 / (2 * ((m : ℝ) + 1)))) := by
          have h2 : Real.exp (-(1 / ((m : ℝ) + 1)))
              = (Real.exp (-(1 / (2 * ((m : ℝ) + 1))))) ^ 2 := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
          rw [h2, Real.sqrt_sq (Real.exp_pos _).le]
  have hpow : (Real.sqrt ((m : ℝ) / ((m : ℝ) + 1))) ^ m
      ≤ Real.exp (-((m : ℝ) / (2 * ((m : ℝ) + 1)))) := by
    calc (Real.sqrt ((m : ℝ) / ((m : ℝ) + 1))) ^ m
        ≤ (Real.exp (-(1 / (2 * ((m : ℝ) + 1))))) ^ m :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hs m
      _ = Real.exp (-((m : ℝ) / (2 * ((m : ℝ) + 1)))) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  refine hpow.trans ?_
  have hexp : -((m : ℝ) / (2 * ((m : ℝ) + 1))) ≤ -(1/2 : ℝ) + (1:ℝ)/42 := by
    rw [neg_le, show -(-(1/2 : ℝ) + (1:ℝ)/42) = (1:ℝ)/2 - (1:ℝ)/42 by ring,
      show (1:ℝ)/2 - (1:ℝ)/42 = 10/21 by norm_num, le_div_iff₀ (by positivity)]
    nlinarith [hm0]
  calc Real.exp (-((m : ℝ) / (2 * ((m : ℝ) + 1))))
      ≤ Real.exp (-(1/2 : ℝ) + (1:ℝ)/42) := Real.exp_le_exp.2 hexp
    _ = Real.exp (-(1/2 : ℝ)) * Real.exp ((1:ℝ)/42) := Real.exp_add _ _
    _ ≤ 0.6066 * (42/41) := by
        have h1 := exp_neg_half_le
        have h2 := exp_inv_fortytwo_le
        have hp1 : 0 < Real.exp (-(1/2 : ℝ)) := Real.exp_pos _
        have hp2 : 0 < Real.exp ((1:ℝ)/42) := Real.exp_pos _
        nlinarith [h1, h2, hp1, hp2]
    _ ≤ 0.6215 := by norm_num


/-! ## §8  The cap bound, assembled -/

/-- **The core estimate.**  Below the crossover height the ball beats the cone by at least
`16/25` of the ball's whole cross-sectional mass. -/
theorem key {m : ℕ} (hm : 20 ≤ m) :
    (16/25 : ℝ) * P (m + 1) ≤ ∫ s in (-(s0 m))..(s0 m), (chord m s - spike m s) := by
  have hm2 : 2 ≤ m := le_trans (by norm_num) hm
  have hmR : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs0 := s0_pos m
  have hs0sq := s0_sq m
  set X := (Real.sqrt ((m : ℝ) / ((m : ℝ) + 1))) ^ m with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXle : X ≤ 0.6215 := coneFactor_le hm
  set B : ℝ := 1 - (m : ℝ) / (6 * ((m : ℝ) + 1)) - X / ((m : ℝ) + 1) with hBdef
  have hBeq : B = (5 * (m : ℝ) + 6 - 6 * X) / (6 * ((m : ℝ) + 1)) := by
    rw [hBdef]; field_simp; ring
  have hB : (0.8116 : ℝ) ≤ B := by
    rw [hBeq, le_div_iff₀ (by positivity)]
    nlinarith [hmR, hXle]
  have hlow : 2 * s0 m * B ≤ ∫ s in (-(s0 m))..(s0 m), (chord m s - spike m s) := by
    have hsplit : (∫ s in (-(s0 m))..(s0 m), (chord m s - spike m s))
        = (∫ s in (-(s0 m))..(s0 m), chord m s) - ∫ s in (-(s0 m))..(s0 m), spike m s :=
      intervalIntegral.integral_sub ((continuous_chord m).intervalIntegrable _ _)
        ((continuous_spike m).intervalIntegrable _ _)
    rw [hsplit, integral_spike, ← hXdef]
    have hc := integral_chord_ge hm2
    have harith : 2 * s0 m * B
        = (2 * s0 m - (m : ℝ) / 3 * (s0 m) ^ 3) - 2 * X * s0 m / ((m : ℝ) + 1) := by
      rw [hBdef, show (s0 m) ^ 3 = s0 m * (s0 m) ^ 2 by ring, hs0sq]
      field_simp; ring
    rw [harith]; linarith [hc]
  refine le_trans ?_ hlow
  have hP := P_pos (m + 1)
  have hPsq := P_sq_le m
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hA : (0 : ℝ) ≤ 16 / 25 * P (m + 1) := by positivity
  have hB0 : (0 : ℝ) ≤ 2 * s0 m * B := by nlinarith [hs0, hB]
  rw [← pow_le_pow_iff_left₀ hA hB0 (by norm_num : (2:ℕ) ≠ 0)]
  have h1 : ((16 / 25 : ℝ) * P (m + 1)) ^ 2 = 256 / 625 * P (m + 1) ^ 2 := by ring
  have h2 : (2 * s0 m * B) ^ 2 = 4 * (s0 m) ^ 2 * B ^ 2 := by ring
  rw [h1, h2, hs0sq]
  have hcore : (512 / 625 : ℝ) * π ≤ 4 * B ^ 2 := by nlinarith [hpi, hB]
  have hNinv : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  calc (256 / 625 : ℝ) * P (m + 1) ^ 2
      ≤ 256 / 625 * (2 * π / ((m : ℝ) + 1)) := by nlinarith [hPsq]
    _ = (1 / ((m : ℝ) + 1)) * (512 / 625 * π) := by ring
    _ ≤ (1 / ((m : ℝ) + 1)) * (4 * B ^ 2) := by nlinarith [hcore, hNinv]
    _ = 4 * (1 / ((m : ℝ) + 1)) * B ^ 2 := by ring

/-- **The real-integral form of the cap bound.** -/
theorem integral_min_le {m : ℕ} (hm : 20 ≤ m) :
    (∫ s : ℝ, min (spike m s) (chord m s)) ≤ 9 / 25 * ∫ s in (-1:ℝ)..1, chord m s := by
  have hm0 : m ≠ 0 := by omega
  have hs0 := s0_pos m
  have hchordR : (∫ s : ℝ, chord m s) = ∫ s in (-1:ℝ)..1, chord m s := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun s hs => chord_eq_zero hm0 hs)]
  have hdiff : (∫ s : ℝ, (chord m s - min (spike m s) (chord m s)))
      = ∫ s in (-(s0 m))..(s0 m), (chord m s - spike m s) := by
    have hpt : (fun s : ℝ => chord m s - min (spike m s) (chord m s))
        = Set.indicator (Set.Icc (-(s0 m)) (s0 m)) (fun t => chord m t - spike m t) := by
      funext s
      rw [chord_sub_min hm0 s, crossover_eq m]
    rw [hpt, MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-(s0 m)) ≤ s0 m)]
  have hlin : (∫ s : ℝ, (chord m s - min (spike m s) (chord m s)))
      = (∫ s : ℝ, chord m s) - ∫ s : ℝ, min (spike m s) (chord m s) :=
    MeasureTheory.integral_sub (integrable_chord hm0) (integrable_min hm0)
  have hk := key hm
  rw [← integral_chord m] at hk
  rw [hdiff] at hlin
  rw [hchordR] at hlin
  linarith [hk, hlin]

/-- **The cone occupies at most `9/25` of the unit ball, from dimension `21` on.** -/
theorem volume_cone_le_of_21 {n : ℕ} [NeZero n] (hn : 21 ≤ n) :
    volume ({x : Fin n → ℝ | ∑ i, x i ^ 2 < (n : ℝ) * x 0 ^ 2}
        ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1})
      ≤ ENNReal.ofReal (9 / 25) * volume {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 20 ≤ m := by omega
  have hm0 : m ≠ 0 := by omega
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast, sliceConeVol hm0, sliceBallVol hm0, lintegral_chord hm0, lintegral_min hm0,
    ← mul_assoc]
  refine mul_le_mul_left ?_ (unitVol m)
  rw [← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact integral_min_le hm

end CapSlice

/-! ## The cap estimate -/

section Main

/-- The set `{x : ‖x‖² < n·x₀²}` is a cone. -/
theorem smul_cone_eq (n : ℕ) [NeZero n] {r : ℝ} (hr : 0 < r) :
    r • {x : Fin n → ℝ | ∑ i, x i ^ 2 < (n : ℝ) * x 0 ^ 2}
      = {x : Fin n → ℝ | ∑ i, x i ^ 2 < (n : ℝ) * x 0 ^ 2} := by
  have key : ∀ (s : ℝ) (y : Fin n → ℝ), ∑ i, (s • y) i ^ 2 = s ^ 2 * ∑ i, y i ^ 2 := by
    intro s y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul, mul_pow]
  have hzero : ∀ (s : ℝ) (y : Fin n → ℝ), (s • y) 0 = s * y 0 := fun s y => rfl
  ext x
  simp only [Set.mem_smul_set, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [key, hzero, mul_pow]
    nlinarith [pow_pos hr 2]
  · intro hx
    refine ⟨r⁻¹ • x, ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
    rw [key, hzero, mul_pow]
    have hinv : (0 : ℝ) < r⁻¹ ^ 2 := by positivity
    nlinarith [hx, hinv]

/-- **The Gaussian mass of the cone is at most `9/25` of the total**, once the dimension is at
least `1100`.  This is the union bound: either the first coordinate is at least `23/25`
(a one-dimensional Gaussian tail, bounded by `gauss_tail_le`) or the remaining `m`
coordinates have an atypically small square sum (bounded by the Chernoff estimate
`lintegral_gauss_shell_le` at `λ = 9/100`). -/
theorem lintegral_gauss_cone_le_ratio {m : ℕ} (hm : 1099 ≤ m) :
    ∫⁻ x in {x : Fin (m + 1) → ℝ | ∑ i, x i ^ 2 < ((m : ℝ) + 1) * x 0 ^ 2},
        ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2))
      ≤ ENNReal.ofReal (9 / 25)
        * ∫⁻ x : Fin (m + 1) → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / 2)) := by
  set S : ℝ := Real.sqrt (2 * Real.pi) with hS
  set T : ℝ := Real.sqrt (Real.pi / ((9 / 100 : ℝ) + 1 / 2)) with hT
  set A : ℝ := ∫ t : ℝ, Set.indicator {t : ℝ | (23 / 25 : ℝ) ≤ |t|}
    (fun t => Real.exp (-(t ^ 2) / 2)) t with hA
  have hSpos : 0 < S := sqrt_two_pi_pos
  have hTpos : 0 ≤ T := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact integral_nonneg fun t => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) t
  have hSm : (0 : ℝ) ≤ S ^ m := by positivity
  refine le_trans (lintegral_gauss_cone_le m (c := 23 / 25) (lam := 9 / 100) (by norm_num)) ?_
  rw [lintegral_gauss_univ, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the Chernoff factor
  have hK : Real.exp ((9 / 100 : ℝ) * ((m : ℝ) * (23 / 25 : ℝ) ^ 2)) * T ^ m
      ≤ 0.0022 * S ^ m := by
    have hrw : Real.exp ((9 / 100 : ℝ) * ((m : ℝ) * (23 / 25 : ℝ) ^ 2))
        = Real.exp ((9 / 100 : ℝ) * (23 / 25 : ℝ) ^ 2) ^ m := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hrw, ← mul_pow]
    calc (Real.exp ((9 / 100 : ℝ) * (23 / 25 : ℝ) ^ 2) * T) ^ m
        ≤ (0.994 * S) ^ m := by
          refine pow_le_pow_left₀ (by positivity) ?_ m
          rw [hT, hS]
          exact chernoff_factor_le
      _ = (0.994 : ℝ) ^ m * S ^ m := by rw [mul_pow]
      _ ≤ 0.0022 * S ^ m := by
          exact mul_le_mul_of_nonneg_right (pow_contraction_le hm) hSm
  have htail : A ≤ S - 1.6103 := gauss_tail_le
  have hSle : S ≤ 2.50663 := sqrt_two_pi_le
  have hfinal : A * S ^ m + Real.exp ((9 / 100 : ℝ) * ((m : ℝ) * (23 / 25 : ℝ) ^ 2)) * S * T ^ m
      ≤ 9 / 25 * S ^ (m + 1) := by
    have hrearr : Real.exp ((9 / 100 : ℝ) * ((m : ℝ) * (23 / 25 : ℝ) ^ 2)) * S * T ^ m
        = S * (Real.exp ((9 / 100 : ℝ) * ((m : ℝ) * (23 / 25 : ℝ) ^ 2)) * T ^ m) := by ring
    rw [hrearr, pow_succ S m]
    have h1 : A * S ^ m ≤ (S - 1.6103) * S ^ m := mul_le_mul_of_nonneg_right htail hSm
    have h2 : S * (Real.exp ((9 / 100 : ℝ) * ((m : ℝ) * (23 / 25 : ℝ) ^ 2)) * T ^ m)
        ≤ S * (0.0022 * S ^ m) := mul_le_mul_of_nonneg_left hK hSpos.le
    have hmain : (0.6422 : ℝ) * S ≤ 1.6103 := by nlinarith [hSle]
    nlinarith [h1, h2, mul_nonneg hSm (sub_nonneg.2 hmain)]
  exact hfinal

/-- **The cone occupies at most `9/25` of the unit ball**, from dimension `21` on.

⚠ **The threshold was `1100` until 2026-08-19.**  It is now `21`, and the proof is the exact
cross-section computation of `section CapSlice` rather than the Gaussian union bound: see that
section's docstring for why retuning the union bound could not get here. -/
theorem volume_cone_le {n : ℕ} [NeZero n] (hn : 21 ≤ n) :
    volume ({x : Fin n → ℝ | ∑ i, x i ^ 2 < (n : ℝ) * x 0 ^ 2}
        ∩ {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1})
      ≤ ENNReal.ofReal (9 / 25) * volume {x : Fin n → ℝ | ∑ i, x i ^ 2 < 1} :=
  volume_cone_le_of_21 hn

/-- **The spherical-cap estimate.**  For `n ≥ 1100` the set of directions `θ` with
`√n·|⟨θ, w⟩| > |w|` — the paper's `A₂`, the cap it bounds by the (incorrect) `1/6` — has
normalised surface measure at most `9/25 = 0.36`.

The true value decreases from `1/2` at `n = 2` to `2(1 − Φ(1)) = 0.31731…`; the bound `0.36`
is therefore honest but not sharp, and the threshold `1100` is an artifact of the union bound
used in the proof, not of the statement (which is true from `n = 5` on). -/
theorem unifSphere_cap_le {n : ℕ} (hn : 21 ≤ n) (w : EuclideanSpace ℝ (Fin n)) :
    unifSphere n {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ‖w‖ < Real.sqrt n * |⟪(θ : EuclideanSpace ℝ (Fin n)), w⟫|}
      ≤ ENNReal.ofReal (9 / 25) := by
  haveI : NeZero n := ⟨by omega⟩
  rcases eq_or_ne w 0 with rfl | hw
  · have hempty : {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ‖(0 : EuclideanSpace ℝ (Fin n))‖ < Real.sqrt n *
          |⟪(θ : EuclideanSpace ℝ (Fin n)), (0 : EuclideanSpace ℝ (Fin n))⟫|} = ∅ := by
      ext θ
      simp
    rw [hempty, measure_empty]
    exact bot_le
  · have hunit : ‖‖w‖⁻¹ • w‖ = 1 := norm_smul_inv_norm hw
    have hunit0 : ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simp
    have hBm : MeasurableSet {t : ℝ | 1 < (n : ℝ) * t ^ 2} :=
      measurableSet_lt measurable_const (by fun_prop)
    rw [almostOrthogonalDir_eq hw, unifSphere, Measure.smul_apply, smul_eq_mul,
      toSphere_setOf_inner_congr hunit hunit0 hBm]
    calc (sphereArea n)⁻¹ * (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
          {θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
            ⟪(θ : EuclideanSpace ℝ (Fin n)),
              EuclideanSpace.single (0 : Fin n) (1 : ℝ)⟫ ∈ {t : ℝ | 1 < (n : ℝ) * t ^ 2}}
        ≤ (sphereArea n)⁻¹ * (ENNReal.ofReal (9 / 25) * sphereArea n) := by
          exact mul_le_mul_right (toSphere_cap_le_of_volume_le (volume_cone_le hn)) _
      _ = ENNReal.ofReal (9 / 25) := by
          rw [mul_comm (ENNReal.ofReal (9 / 25)), ← mul_assoc,
            ENNReal.inv_mul_cancel sphereArea_ne_zero (sphereArea_ne_top n), one_mul]

/-- **The cap hypothesis `hcap` of `tvLe_hitAndRun_lemma41`, discharged at `q₂ = 9/25`.**
This is the shape the capstone consumes. -/
theorem hitAndRun_almostOrthogonal_le_nine_twentyfifths {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (u v : EuclideanSpace ℝ (Fin n)) :
    hitAndRun K u {x : EuclideanSpace ℝ (Fin n) |
        ‖x - u‖ * ‖u - v‖ < Real.sqrt n * |⟪x - u, u - v⟫|}
      ≤ ENNReal.ofReal (9 / 25) :=
  (hitAndRun_almostOrthogonal_le hK u v).trans (unifSphere_cap_le hn (u - v))

/-- **Lemma 4.1 with every hypothesis of the paper's proof discharged**, for `n ≥ 1100`.

`tvLe_hitAndRun_lemma41_of_le_three_eighths` at `q₂ = 9/25 < 3/8` gives the numeral
`1 − 1/8000`: the one-step laws of two points at cross-ratio distance `< 1/8` overlap in
mass at least `1/8000`.  (The paper claims `1/500`; see the module docstring of
`HitAndRunOverlap.lean` for why no rounding recovers it, and this file's docstring for why
`1/8000` rather than the `1/1892` that a sharp cap bound would give.) -/
theorem tvLe_hitAndRun_lemma41_uncond {n : ℕ} (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (hmoveu : hitAndRunProposal K u Set.univ = 1)
    (hmovev : hitAndRunProposal K v Set.univ = 1)
    (ha : chordLow K u v < 0) (hb : 1 < chordHigh K u v)
    (hdK : crossRatioDist K u v < 1 / 8)
    (hFu : ‖u - v‖ < 2 / Real.sqrt n * medianStep K u) :
    TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 8000)) := by
  have h := tvLe_hitAndRun_lemma41_of_le_three_eighths (n := n) (by omega) hKc hKcl hKm hKb
    hu hv huv hmoveu hmovev ha hb hdK hFu (q₂ := 9 / 25) (by norm_num) (by norm_num)
    (hitAndRun_almostOrthogonal_le_nine_twentyfifths hn hKm u v)
  have hnum : (1 : ℝ) - (3 / 8 - 9 / 25) / 120 = 1 - 1 / 8000 := by norm_num
  rwa [hnum] at h

end Main

/-! ### Axiom profile -/

section AxiomCheck

#print axioms measurableSet_sqLt
#print axioms smul_sqLt_one
#print axioms volume_cone_inter_sqLt
#print axioms gaussRadius_nonneg
#print axioms measurable_gaussRadius
#print axioms lt_exp_iff_lt_gaussRadius_sq
#print axioms lintegral_gauss_cone
#print axioms volume_sqLt_one_pos
#print axioms lintegral_ofReal_prod
#print axioms integrable_gauss
#print axioms integrable_gauss_half
#print axioms integral_gauss_half
#print axioms exp_sum_sq
#print axioms lintegral_gauss_univ
#print axioms lintegral_gauss_slab
#print axioms lintegral_gauss_shell_le
#print axioms smul_univ_eq
#print axioms volume_cone_inter_le_of_lintegral_le
#print axioms lintegral_gauss_cone_le
#print axioms smul_image_cap_eq
#print axioms preimage_ofLp_cone
#print axioms toSphere_cap_le_of_volume_le
#print axioms poly_le_gauss
#print axioms integral_poly
#print axioms gauss_tail_le
#print axioms sqrt_two_pi_le
#print axioms sqrt_two_pi_pos
#print axioms exp_lam_le
#print axioms chernoff_factor_le
#print axioms pow_contraction_le
#print axioms smul_cone_eq
#print axioms lintegral_gauss_cone_le_ratio
#print axioms volume_cone_le
#print axioms unifSphere_cap_le
#print axioms hitAndRun_almostOrthogonal_le_nine_twentyfifths
#print axioms tvLe_hitAndRun_lemma41_uncond

end AxiomCheck

end Arlib.MarkovChains
