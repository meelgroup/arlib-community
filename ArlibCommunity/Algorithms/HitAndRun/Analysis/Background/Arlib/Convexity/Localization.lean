/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.PrekopaLeindlerN
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Isoperimetry

/-!
# Marginals of log-concave functions, and log-concave measures

This file collects what the Prékopa–Leindler inequality of
`Arlib.Convexity.PrekopaLeindlerN` unlocks: the **marginal theorem** — integrating a
log-concave function over some of its variables leaves a log-concave function — and its
standard consequences.  Mathlib `v4.32` has none of them.

## Main results

* `Arlib.isLogConcave_marginal_pi` and `Arlib.isLogConcave_marginal_real` — **marginals of
  log-concave functions are log-concave**, for a fibre `ℝᵐ` resp. `ℝ`.  These are the
  workhorses; everything else in the file is a corollary of one of them or of their
  `ℝ≥0∞` analogue.
* `Arlib.isLogConcave_snoc_marginal` — the headline shape: for log-concave
  `G : ℝⁿ⁺¹ → ℝ`, the function `x ↦ ∫ t, G (Fin.snoc x t)` is log-concave on `ℝⁿ`.
* `Arlib.isLogConcave_convolution` — **the convolution of two log-concave functions is
  log-concave**.
* `Arlib.IsLogConcaveENN` — log-concavity for `ℝ≥0∞`-valued functions, with
  `Arlib.isLogConcaveENN_marginal_pi`, the marginal theorem in the form that needs **no**
  integrability hypothesis, and `Arlib.isLogConcaveENN_ofReal` bridging to the real-valued
  notion.
* `Arlib.IsLogConcaveENN.setLIntegral_geom_le` — **a measure with a log-concave density is
  a log-concave measure** (Prékopa, Borell): `μ(A)^λ · μ(B)^(1−λ) ≤ μ(λA + (1−λ)B)`.
  `Arlib.brunn_minkowski_pi` is its `F = 1` case.
* `Arlib.isLogConcaveENN_fiber_volume` and `Arlib.isLogConcaveENN_section_volume` — the
  fibre-volume function of a convex body is log-concave (Brunn's theorem, log-concave
  form).
* `Arlib.fst_withDensity_prod` together with `Arlib.isLogConcaveENN_marginal_prod` — **the
  marginals of a log-concave measure are log-concave**: the first marginal of
  `(μ ⊗ ν).withDensity F` is `μ.withDensity` of the marginal density `x ↦ ∫⁻ t, F (x,t)`,
  and that density is log-concave whenever `F` is.

## Why the integrability hypotheses

The Bochner-integral statements carry `∀ x, Integrable (G x)`.  This is not slack: `∫`
returns the junk value `0` on a non-integrable function, so without it the inequality
`(∫ G x)^a (∫ G y)^b ≤ ∫ G (a•x + b•y)` is simply false — take `G` with an integrable
slice at `x` and `y` and a non-integrable slice at the midpoint.  The `ℝ≥0∞` statements
have no such hypothesis, which is why the indicator and fibre-volume corollaries are
stated there.

## What this file does NOT contain

The **Localization Lemma** of Lovász–Simonovits and the **isoperimetric inequality for
log-concave densities** (Cousins–Vempala §3, `thm:iso`) are *not* proved here, and — as in
`Arlib.Convexity.Isoperimetry` — **no predicate in this file asserts either of them**.
There is deliberately no `LocalizationInput`, `IsoInput` or `OneDimIso`: a predicate whose
name asserts a theorem is inhabited only by degenerate witnesses and establishes nothing
where the conclusion has content (`CV-ROADMAP.md` §2a).

What is proved above is the *input* side of the localisation argument — Prékopa–Leindler's
marginal theorem and the log-concavity of the measures and section functions the argument
manipulates.  What remains is the localisation induction itself (a compactness/bisection
argument over the space of needles) and the one-dimensional isoperimetric inequality of
Kannan–Lovász–Simonovits (KLS95 Theorem 5.1).  Neither is stated below, in Lean or as a
predicate.

## References

* Prékopa, *On logarithmic concave measures and functions*, 1973.
* Lovász and Simonovits, *Random walks in a convex body and an improved volume algorithm*,
  1993, §2 (the Localization Lemma).
* Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian
  Volume*, §3.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Arlib

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **Log-concavity is preserved by precomposition with a linear map.** -/
theorem IsLogConcave.comp_linearMap {f : F → ℝ} (hf : IsLogConcave f) (L : E →ₗ[ℝ] F) :
    IsLogConcave (fun x => f (L x)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  show f (L x) ^ a * f (L y) ^ b ≤ f (L (a • x + b • y))
  rw [map_add, map_smul, map_smul]
  exact hf.geom_le _ _ ha hb hab

/-! ### Marginals -/

/-- **Marginals of log-concave functions are log-concave** (fibre `Fin m → ℝ`).

If `F : E → (Fin m → ℝ) → ℝ` is nonnegative, log-concave as a function on the product
`E × (Fin m → ℝ)`, and has measurable integrable slices, then

  `x ↦ ∫ t, F x t`

is log-concave on `E`.  This is the classical corollary of Prékopa–Leindler; it is
`Arlib.prekopa_leindler_pi` applied to the three slices `F x`, `F y` and `F (a • x + b • y)`. -/
theorem isLogConcave_marginal_pi {m : ℕ} {G : E → (Fin m → ℝ) → ℝ}
    (hlc : IsLogConcave (fun p : E × (Fin m → ℝ) => G p.1 p.2))
    (hnn : ∀ x t, 0 ≤ G x t) (hmeas : ∀ x, Measurable (G x)) (hint : ∀ x, Integrable (G x)) :
    IsLogConcave (fun x => ∫ t, G x t) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  show (∫ t, G x t) ^ a * (∫ t, G y t) ^ b ≤ ∫ t, G (a • x + b • y) t
  rcases ha.lt_or_eq with ha' | ha'
  swap
  · have hb1 : b = 1 := by linarith
    subst hb1
    have : a = 0 := ha'.symm
    subst this
    simp
  rcases hb.lt_or_eq with hb' | hb'
  swap
  · have ha1 : a = 1 := by linarith
    subst ha1
    have : b = 0 := hb'.symm
    subst this
    simp
  have hb'' : b = 1 - a := by linarith
  subst hb''
  refine prekopa_leindler_pi ha' (by linarith) (hmeas x) (hmeas y) (hmeas _)
    (hnn x) (hnn y) (hint x) (hint y) (hint _) ?_
  intro s u
  have := hlc.geom_le (x, s) (y, u) ha hb hab
  simpa [Prod.smul_mk, Prod.mk_add_mk] using this

/-- **Marginals of log-concave functions are log-concave** (fibre `ℝ`).

Same statement as `Arlib.isLogConcave_marginal_pi` with the one-dimensional fibre `ℝ`; it
uses the one-dimensional Prékopa–Leindler inequality directly. -/
theorem isLogConcave_marginal_real {G : E → ℝ → ℝ}
    (hlc : IsLogConcave (fun p : E × ℝ => G p.1 p.2))
    (hnn : ∀ x t, 0 ≤ G x t) (hmeas : ∀ x, Measurable (G x)) (hint : ∀ x, Integrable (G x)) :
    IsLogConcave (fun x => ∫ t, G x t) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  show (∫ t, G x t) ^ a * (∫ t, G y t) ^ b ≤ ∫ t, G (a • x + b • y) t
  rcases ha.lt_or_eq with ha' | ha'
  swap
  · have hb1 : b = 1 := by linarith
    subst hb1
    have : a = 0 := ha'.symm
    subst this
    simp
  rcases hb.lt_or_eq with hb' | hb'
  swap
  · have ha1 : a = 1 := by linarith
    subst ha1
    have : b = 0 := hb'.symm
    subst this
    simp
  have hb'' : b = 1 - a := by linarith
  subst hb''
  refine prekopa_leindler_one_dim ha' (by linarith) (hmeas x) (hmeas y) (hmeas _)
    (hnn x) (hnn y) (hint x) (hint y) (hint _) ?_
  intro s u
  have := hlc.geom_le (x, s) (y, u) ha hb hab
  simpa [Prod.smul_mk, Prod.mk_add_mk] using this

/-! ### The last-coordinate marginal on `Fin (n+1) → ℝ` -/

/-- `Fin.snoc` respects two-term linear combinations. -/
theorem snoc_linear {n : ℕ} (a b : ℝ) (x y : Fin n → ℝ) (s u : ℝ) :
    (Fin.snoc (a • x + b • y) (a * s + b * u) : Fin (n + 1) → ℝ)
      = a • (Fin.snoc x s : Fin (n + 1) → ℝ) + b • (Fin.snoc y u : Fin (n + 1) → ℝ) := by
  funext k
  induction k using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- Appending a coordinate is measurable in the appended coordinate. -/
theorem measurable_snoc {n : ℕ} (x : Fin n → ℝ) :
    Measurable fun t : ℝ => (Fin.snoc x t : Fin (n + 1) → ℝ) := by
  refine measurable_pi_lambda _ fun i => ?_
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact measurable_id
  | cast j => simp

/-- Log-concavity of a function on `Fin (n+1) → ℝ` transfers to the "split" function on
`(Fin n → ℝ) × ℝ` obtained by appending the last coordinate. -/
theorem IsLogConcave.comp_snoc {n : ℕ} {G : (Fin (n + 1) → ℝ) → ℝ} (hG : IsLogConcave G) :
    IsLogConcave (fun p : (Fin n → ℝ) × ℝ => G (Fin.snoc p.1 p.2)) := by
  refine ⟨convex_univ, fun p _ q _ a b ha hb hab => ?_⟩
  show G (Fin.snoc p.1 p.2) ^ a * G (Fin.snoc q.1 q.2) ^ b
    ≤ G (Fin.snoc (a • p + b • q).1 (a • p + b • q).2)
  have h1 : (a • p + b • q).1 = a • p.1 + b • q.1 := rfl
  have h2 : (a • p + b • q).2 = a * p.2 + b * q.2 := rfl
  rw [h1, h2, snoc_linear]
  exact hG.geom_le _ _ ha hb hab

/-- **The marginal of a log-concave function in its last coordinate is log-concave.**

If `G : (Fin (n+1) → ℝ) → ℝ` is measurable, nonnegative and log-concave, and each slice
`t ↦ G (Fin.snoc x t)` is integrable, then

  `x ↦ ∫ t, G (Fin.snoc x t)`

is a log-concave function on `Fin n → ℝ`.

This is the classical Prékopa–Leindler corollary.  Mathlib `v4.32` has neither it nor the
inequality it rests on. -/
theorem isLogConcave_snoc_marginal {n : ℕ} {G : (Fin (n + 1) → ℝ) → ℝ}
    (hlc : IsLogConcave G) (hnn : ∀ z, 0 ≤ G z) (hGm : Measurable G)
    (hint : ∀ x : Fin n → ℝ, Integrable fun t : ℝ => G (Fin.snoc x t)) :
    IsLogConcave (fun x : Fin n → ℝ => ∫ t, G (Fin.snoc x t)) :=
  isLogConcave_marginal_real hlc.comp_snoc (fun _ _ => hnn _)
    (fun x => hGm.comp (measurable_snoc x)) hint

/-! ### Convolution -/

/-- The integrand of a convolution, `(x, y) ↦ f y * g (x - y)`, is log-concave on the
product whenever `f` and `g` are log-concave and nonnegative: it is a product of two
log-concave functions precomposed with the linear maps `(x,y) ↦ y` and `(x,y) ↦ x - y`. -/
theorem isLogConcave_convolution_integrand {f g : E → ℝ} (hf : IsLogConcave f)
    (hg : IsLogConcave g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    IsLogConcave (fun p : E × E => f p.2 * g (p.1 - p.2)) := by
  have h1 : IsLogConcave (fun p : E × E => f p.2) :=
    hf.comp_linearMap (LinearMap.snd ℝ E E)
  have h2 : IsLogConcave (fun p : E × E => g (p.1 - p.2)) :=
    hg.comp_linearMap (LinearMap.fst ℝ E E - LinearMap.snd ℝ E E)
  exact h1.mul h2 (fun _ => hf0 _) (fun _ => hg0 _)

/-- **The convolution of two log-concave functions is log-concave.**

For nonnegative measurable log-concave `f g : (Fin n → ℝ) → ℝ` whose convolution integrand
is integrable at every point,

  `x ↦ ∫ y, f y * g (x - y)`

is log-concave.  This is `Arlib.isLogConcave_marginal_pi` applied to the integrand, whose
log-concavity on the product is `Arlib.isLogConcave_convolution_integrand`. -/
theorem isLogConcave_convolution {n : ℕ} {f g : (Fin n → ℝ) → ℝ} (hf : IsLogConcave f)
    (hg : IsLogConcave g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : Measurable f) (hgm : Measurable g)
    (hint : ∀ x : Fin n → ℝ, Integrable fun y => f y * g (x - y)) :
    IsLogConcave (fun x : Fin n → ℝ => ∫ y, f y * g (x - y)) :=
  isLogConcave_marginal_pi (isLogConcave_convolution_integrand hf hg hf0 hg0)
    (fun _ _ => mul_nonneg (hf0 _) (hg0 _))
    (fun _ => hfm.mul (hgm.comp (measurable_const.sub measurable_id))) hint

/-! ### The `ℝ≥0∞`-valued formulation

The Bochner statements above need an integrability hypothesis on *every* slice, because a
non-integrable slice makes `∫` return the junk value `0` and the inequality can then fail.
The lower-Lebesgue formulation has no such hypothesis, which is what makes it usable for
indicator functions and for marginals of measures. -/

/-- **Log-concavity for `ℝ≥0∞`-valued functions.**

`f x ^ a * f y ^ b ≤ f (a • x + b • y)` for all weights `a, b ≥ 0` with `a + b = 1`, with
`ENNReal.rpow`.  This is the exact analogue of `Arlib.IsLogConcave`; the two are related by
`Arlib.isLogConcaveENN_ofReal`. -/
def IsLogConcaveENN (f : E → ℝ≥0∞) : Prop :=
  ∀ x y : E, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f x ^ a * f y ^ b ≤ f (a • x + b • y)

/-- A nonnegative log-concave real function becomes an `ℝ≥0∞`-valued log-concave function
under `ENNReal.ofReal`. -/
theorem isLogConcaveENN_ofReal {f : E → ℝ} (hf : IsLogConcave f) (hf0 : ∀ x, 0 ≤ f x) :
    IsLogConcaveENN (fun x => ENNReal.ofReal (f x)) := by
  intro x y a b ha hb hab
  rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ha, ENNReal.ofReal_rpow_of_nonneg (hf0 y) hb,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) a)]
  exact ENNReal.ofReal_le_ofReal (hf.geom_le x y ha hb hab)

/-- **Marginals of `ℝ≥0∞`-valued log-concave functions are log-concave**, with no
integrability hypothesis at all.  This is `Arlib.prekopa_leindler_lintegral_pi` applied to
the three slices. -/
theorem isLogConcaveENN_marginal_pi {m : ℕ} {G : E → (Fin m → ℝ) → ℝ≥0∞}
    (hlc : IsLogConcaveENN (fun p : E × (Fin m → ℝ) => G p.1 p.2))
    (hmeas : ∀ x, Measurable (G x)) :
    IsLogConcaveENN (fun x => ∫⁻ t, G x t) := by
  intro x y a b ha hb hab
  rcases ha.lt_or_eq with ha' | ha'
  swap
  · have hb1 : b = 1 := by linarith
    subst hb1
    have h0 : a = 0 := ha'.symm
    subst h0
    simp
  rcases hb.lt_or_eq with hb' | hb'
  swap
  · have ha1 : a = 1 := by linarith
    subst ha1
    have h0 : b = 0 := hb'.symm
    subst h0
    simp
  have hb'' : b = 1 - a := by linarith
  subst hb''
  refine prekopa_leindler_lintegral_pi m a ha' (by linarith) _ _ _ (hmeas x) (hmeas y)
    (hmeas _) ?_
  intro s u
  have := hlc (x, s) (y, u) a (1 - a) ha hb hab
  simpa [Prod.smul_mk, Prod.mk_add_mk] using this

/-- **The indicator of a convex set is log-concave**, in `ℝ≥0∞` form. -/
theorem isLogConcaveENN_indicator {s : Set E} (hs : Convex ℝ s) :
    IsLogConcaveENN (Set.indicator s (1 : E → ℝ≥0∞)) := by
  intro x y a b ha hb hab
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · have hz : a • x + b • y ∈ s := hs hx hy ha hb hab
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
    · rcases eq_or_ne b 0 with rfl | hb'
      · have ha1 : a = 1 := by linarith
        subst ha1
        simp [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos (hb.lt_of_ne' hb'), mul_zero]
        exact zero_le
  · rcases eq_or_ne a 0 with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1
      simp
    · rw [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos (ha.lt_of_ne' ha'), zero_mul]
      exact zero_le

section FiberVolume

variable [MeasurableSpace E]

/-- **The fibre-volume function of a convex body is log-concave.**

For a convex measurable `K ⊆ E × ℝᵐ`, the function `x ↦ vol {t | (x, t) ∈ K}` is
log-concave.  Taking `E = ℝⁿ` and `m = 1` this is the statement that the length of the
vertical section of a convex body is a log-concave function of the base point; it is the
indicator special case of `Arlib.isLogConcaveENN_marginal_pi`, and no integrability or
boundedness hypothesis is needed. -/
theorem isLogConcaveENN_fiber_volume {m : ℕ} {K : Set (E × (Fin m → ℝ))}
    (hconv : Convex ℝ K) (hK : MeasurableSet K) :
    IsLogConcaveENN (fun x : E => volume (Prod.mk x ⁻¹' K)) := by
  have hfib : ∀ x : E, MeasurableSet (Prod.mk x ⁻¹' K) :=
    fun x => hK.preimage measurable_prodMk_left
  have hslice : ∀ x : E,
      (fun t : Fin m → ℝ => Set.indicator K (1 : E × (Fin m → ℝ) → ℝ≥0∞) (x, t))
        = Set.indicator (Prod.mk x ⁻¹' K) (1 : (Fin m → ℝ) → ℝ≥0∞) := by
    intro x
    funext t
    by_cases ht : (x, t) ∈ K
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ Prod.mk x ⁻¹' K from ht)]
      rfl
    · rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (show t ∉ Prod.mk x ⁻¹' K from ht)]
  have hmain := isLogConcaveENN_marginal_pi
    (G := fun (x : E) (t : Fin m → ℝ) => Set.indicator K (1 : E × (Fin m → ℝ) → ℝ≥0∞) (x, t))
    (isLogConcaveENN_indicator hconv)
    (fun x => by rw [hslice x]; exact measurable_one.indicator (hfib x))
  have heq : (fun x : E => ∫⁻ t, Set.indicator K (1 : E × (Fin m → ℝ) → ℝ≥0∞) (x, t))
      = fun x : E => volume (Prod.mk x ⁻¹' K) := by
    funext x
    rw [hslice x, lintegral_indicator_one (hfib x)]
  rwa [heq] at hmain

end FiberVolume

/-- **Brunn's theorem, log-concave form.**  For a convex measurable body `K ⊆ ℝ × ℝⁿ` the
function sending `t` to the `n`-volume of the section `{y | (t, y) ∈ K}` is log-concave.

This is `Arlib.isLogConcaveENN_fiber_volume` at `E = ℝ`.  (Brunn–Minkowski gives the
sharper statement that the section volume is `1/n`-concave on its support; log-concavity
is the form the localisation literature uses.) -/
theorem isLogConcaveENN_section_volume {n : ℕ} {K : Set (ℝ × (Fin n → ℝ))}
    (hconv : Convex ℝ K) (hK : MeasurableSet K) :
    IsLogConcaveENN fun t : ℝ => volume {y : Fin n → ℝ | (t, y) ∈ K} :=
  isLogConcaveENN_fiber_volume hconv hK

/-- **Non-vacuity witness with content.**  The section-volume theorem applies to a genuine
body: a closed ball of any radius in `ℝ × ℝⁿ`, whose sections are nondegenerate balls for
every `t` strictly inside. -/
theorem isLogConcaveENN_section_volume_closedBall {n : ℕ} (c : ℝ × (Fin n → ℝ)) (r : ℝ) :
    IsLogConcaveENN fun t : ℝ => volume {y : Fin n → ℝ | (t, y) ∈ Metric.closedBall c r} :=
  isLogConcaveENN_section_volume (convex_closedBall c r)
    Metric.isClosed_closedBall.measurableSet

/-! ### A measure with a log-concave density is a log-concave measure -/

section LogConcaveMeasure

open Pointwise

/-- **A measure with a log-concave density is a log-concave measure** (Prékopa, Borell).

For a measurable log-concave `F : ℝⁿ → ℝ≥0∞` and measurable `A`, `B`, `C` with
`lam • A + (1 - lam) • B ⊆ C`,

  `(∫⁻ A F) ^ lam * (∫⁻ B F) ^ (1 - lam) ≤ ∫⁻ C F`.

Taking `F = 1` recovers `Arlib.brunn_minkowski_pi`.  The Minkowski combination is fed in
through a measurable superset `C` because a sum of measurable sets need not be
measurable; `Arlib.IsLogConcaveENN.setLIntegral_geom_le_toMeasurable` instantiates `C`
with the measurable hull. -/
theorem IsLogConcaveENN.setLIntegral_geom_le {n : ℕ} {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) {F : (Fin n → ℝ) → ℝ≥0∞} (hF : IsLogConcaveENN F) (hFm : Measurable F)
    {A B C : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hsub : lam • A + (1 - lam) • B ⊆ C) :
    (∫⁻ x in A, F x) ^ lam * (∫⁻ x in B, F x) ^ (1 - lam) ≤ ∫⁻ x in C, F x := by
  have hlam1' : (0 : ℝ) < 1 - lam := by linarith
  have hyp : ∀ x y : Fin n → ℝ, (A.indicator F) x ^ lam * (B.indicator F) y ^ (1 - lam)
      ≤ (C.indicator F) (lam • x + (1 - lam) • y) := by
    intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hmem : lam • x + (1 - lam) • y ∈ C :=
          hsub (Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy))
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hmem]
        exact hF x y lam (1 - lam) hlam0.le hlam1'.le (by ring)
      · rw [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hlam1', mul_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hlam0, zero_mul]
      exact zero_le
  have key := prekopa_leindler_lintegral_pi n lam hlam0 hlam1 _ _ _ (hFm.indicator hA)
    (hFm.indicator hB) (hFm.indicator hC) hyp
  rwa [lintegral_indicator hA, lintegral_indicator hB, lintegral_indicator hC] at key

/-- `Arlib.IsLogConcaveENN.setLIntegral_geom_le` with the measurable hull of the Minkowski
combination on the right. -/
theorem IsLogConcaveENN.setLIntegral_geom_le_toMeasurable {n : ℕ} {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) {F : (Fin n → ℝ) → ℝ≥0∞} (hF : IsLogConcaveENN F) (hFm : Measurable F)
    {A B : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ x in A, F x) ^ lam * (∫⁻ x in B, F x) ^ (1 - lam)
      ≤ ∫⁻ x in toMeasurable volume (lam • A + (1 - lam) • B), F x :=
  hF.setLIntegral_geom_le hlam0 hlam1 hFm hA hB (measurableSet_toMeasurable _ _)
    (subset_toMeasurable _ _)

/-- The same statement for the measure `volume.withDensity F` itself. -/
theorem IsLogConcaveENN.withDensity_geom_le {n : ℕ} {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) {F : (Fin n → ℝ) → ℝ≥0∞} (hF : IsLogConcaveENN F) (hFm : Measurable F)
    {A B C : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hsub : lam • A + (1 - lam) • B ⊆ C) :
    (volume.withDensity F) A ^ lam * (volume.withDensity F) B ^ (1 - lam)
      ≤ (volume.withDensity F) C := by
  rw [withDensity_apply _ hA, withDensity_apply _ hB, withDensity_apply _ hC]
  exact hF.setLIntegral_geom_le hlam0 hlam1 hFm hA hB hC hsub

end LogConcaveMeasure

/-! ### Marginals of measures -/

section MarginalMeasure

/-- **The first marginal of a measure with a density is the measure whose density is the
marginal of the density.**

`((μ ⊗ ν).withDensity G).fst = μ.withDensity (x ↦ ∫⁻ t, G (x, t) ∂ν)`.  This is Tonelli's
theorem in disguise; it is the measure-theoretic half of "the marginals of a log-concave
measure are log-concave", the other half being
`Arlib.isLogConcaveENN_marginal_prod`. -/
theorem fst_withDensity_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {G : α × β → ℝ≥0∞}
    (hG : Measurable G) :
    ((μ.prod ν).withDensity G).fst = μ.withDensity fun x => ∫⁻ t, G (x, t) ∂ν := by
  refine Measure.ext fun S hS => ?_
  have hpre : Prod.fst ⁻¹' S = S ×ˢ (Set.univ : Set β) := by
    ext p; simp
  rw [Measure.fst_apply hS, withDensity_apply _ (measurable_fst hS), withDensity_apply _ hS,
    hpre, ← Measure.restrict_prod_eq_prod_univ, lintegral_prod _ hG.aemeasurable]

/-- The marginal `x ↦ ∫⁻ t, G (x, t)` of a log-concave `ℝ≥0∞`-valued function on a product
`E × ℝᵐ` is log-concave.  This is `Arlib.isLogConcaveENN_marginal_pi` in uncurried form. -/
theorem isLogConcaveENN_marginal_prod [MeasurableSpace E] {m : ℕ}
    {G : E × (Fin m → ℝ) → ℝ≥0∞}
    (hlc : IsLogConcaveENN G) (hG : Measurable G) :
    IsLogConcaveENN fun x : E => ∫⁻ t, G (x, t) :=
  isLogConcaveENN_marginal_pi (G := fun x t => G (x, t)) hlc
    (fun _ => hG.comp (measurable_const.prodMk measurable_id))

/-- The marginal density of a log-concave density is measurable. -/
theorem measurable_marginal_prod {α : Type*} [MeasurableSpace α] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} [SFinite ν] {G : α × β → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun x : α => ∫⁻ t, G (x, t) ∂ν :=
  hG.lintegral_prod_right'

end MarginalMeasure

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms IsLogConcave.comp_linearMap
#print axioms isLogConcave_marginal_pi
#print axioms isLogConcave_marginal_real
#print axioms snoc_linear
#print axioms measurable_snoc
#print axioms IsLogConcave.comp_snoc
#print axioms isLogConcave_snoc_marginal
#print axioms isLogConcave_convolution_integrand
#print axioms isLogConcave_convolution
#print axioms isLogConcaveENN_ofReal
#print axioms isLogConcaveENN_marginal_pi
#print axioms isLogConcaveENN_indicator
#print axioms isLogConcaveENN_fiber_volume
#print axioms isLogConcaveENN_section_volume
#print axioms isLogConcaveENN_section_volume_closedBall
#print axioms IsLogConcaveENN.setLIntegral_geom_le
#print axioms IsLogConcaveENN.setLIntegral_geom_le_toMeasurable
#print axioms IsLogConcaveENN.withDensity_geom_le
#print axioms fst_withDensity_prod
#print axioms isLogConcaveENN_marginal_prod
#print axioms measurable_marginal_prod

end Arlib
