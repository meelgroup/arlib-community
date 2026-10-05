/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Log-concave functions on a real vector space

Mathlib `v4.32` has no notion of log-concavity for functions on a vector space, so this
file introduces one, in the multiplicative form that the convex-geometry literature uses:

  `f(x)^a · f(y)^b ≤ f(a·x + b·y)`  for `a, b ≥ 0` with `a + b = 1`.

Exponentiation is `Real.rpow`. The multiplicative form is preferred over "the logarithm is
concave" because it handles the zeros of `f` correctly, and the densities of interest —
indicators of convex bodies, Gaussians restricted to a body — do vanish on a set of
positive measure. `Arlib.logConcaveOn_iff_concaveOn_log` recovers the logarithmic
characterisation wherever `f` is strictly positive.

Nonnegativity is *not* bundled into the definition: it is carried as a separate hypothesis
`∀ x ∈ s, 0 ≤ f x` by the lemmas that need it, so that the definition mirrors Mathlib's
`ConvexOn`/`ConcaveOn` exactly and composes with `Real.rpow` lemmas without side
conditions.

## Main definitions

* `Arlib.LogConcaveOn s f` — `f` is log-concave on the convex set `s`.
* `Arlib.IsLogConcave f` — `f` is log-concave on all of `E`.

## Main results

* `Arlib.logConcaveOn_iff_concaveOn_log` — for `f` positive on `s`, log-concavity of `f`
  is equivalent to concavity of `Real.log ∘ f`. This is what makes the definition usable.
* `Arlib.logConcaveOn_exp` — `exp ∘ g` is log-concave when `g` is concave; the
  most-used constructor.
* `Arlib.LogConcaveOn.mul` — products of log-concave functions are log-concave. This is
  the closure property that Gaussian-restricted densities `f · γ` need.
* `Arlib.isLogConcave_indicator_iff` — `Set.indicator s 1` is log-concave iff `s` is
  convex.
* `Arlib.isLogConcave_gaussian` — the Gaussian density `e^{−‖x‖²/(2σ²)}` is log-concave.

## References

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian
Volume*, §3.
-/

namespace Arlib

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The definition -/

/-- **Log-concavity on a set.** `f` is log-concave on `s` when `s` is convex and

  `f x ^ a * f y ^ b ≤ f (a • x + b • y)`

for all `x, y ∈ s` and all weights `a, b ≥ 0` with `a + b = 1`, the exponentiation being
`Real.rpow`.

The shape of the statement deliberately mirrors Mathlib's `ConcaveOn`. Nonnegativity of
`f` is *not* part of the definition; the lemmas that need it take it as a hypothesis. -/
def LogConcaveOn (s : Set E) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f x ^ a * f y ^ b ≤ f (a • x + b • y)

/-- **Log-concavity on the whole space**, i.e. log-concavity on `Set.univ`. -/
def IsLogConcave (f : E → ℝ) : Prop :=
  LogConcaveOn (Set.univ : Set E) f

/-- The domain of a log-concave function is convex. -/
theorem LogConcaveOn.convex {s : Set E} {f : E → ℝ} (hf : LogConcaveOn s f) : Convex ℝ s :=
  hf.1

/-- The defining geometric-mean inequality of `LogConcaveOn`. -/
theorem LogConcaveOn.geom_le {s : Set E} {f : E → ℝ} (hf : LogConcaveOn s f) {x : E}
    (hx : x ∈ s) {y : E} (hy : y ∈ s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f x ^ a * f y ^ b ≤ f (a • x + b • y) :=
  hf.2 hx hy ha hb hab

/-- The defining geometric-mean inequality of `IsLogConcave`, with no membership side
conditions. -/
theorem IsLogConcave.geom_le {f : E → ℝ} (hf : IsLogConcave f) (x y : E) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f x ^ a * f y ^ b ≤ f (a • x + b • y) :=
  hf.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab

/-- Log-concavity on the whole space is exactly log-concavity on `Set.univ`. -/
theorem isLogConcave_iff_logConcaveOn_univ {f : E → ℝ} :
    IsLogConcave f ↔ LogConcaveOn (Set.univ : Set E) f :=
  Iff.rfl

/-- Log-concavity restricts to convex subsets. -/
theorem LogConcaveOn.subset {s t : Set E} {f : E → ℝ} (hf : LogConcaveOn s f) (hts : t ⊆ s)
    (ht : Convex ℝ t) : LogConcaveOn t f :=
  ⟨ht, fun _ hx _ hy _ _ ha hb hab => hf.2 (hts hx) (hts hy) ha hb hab⟩

/-- A globally log-concave function is log-concave on every convex set. -/
theorem IsLogConcave.logConcaveOn {s : Set E} {f : E → ℝ} (hf : IsLogConcave f)
    (hs : Convex ℝ s) : LogConcaveOn s f :=
  LogConcaveOn.subset hf (Set.subset_univ s) hs

/-! ### Constants -/

/-- A nonnegative constant function is log-concave on any convex set. -/
theorem logConcaveOn_const {s : Set E} (hs : Convex ℝ s) {c : ℝ} (hc : 0 ≤ c) :
    LogConcaveOn s (fun _ => c) := by
  refine ⟨hs, fun x _ y _ a b ha hb hab => ?_⟩
  simp only
  rcases hc.lt_or_eq with hpos | h0
  · rw [← Real.rpow_add hpos, hab, Real.rpow_one]
  · subst h0
    rcases eq_or_ne a 0 with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1
      simp
    · simp [Real.zero_rpow ha']

/-- A nonnegative constant function is log-concave. -/
theorem isLogConcave_const {c : ℝ} (hc : 0 ≤ c) : IsLogConcave (fun _ : E => c) :=
  logConcaveOn_const convex_univ hc

/-- The constant function `1` is log-concave. -/
theorem isLogConcave_one : IsLogConcave (1 : E → ℝ) :=
  isLogConcave_const zero_le_one

/-! ### Closure properties -/

/-- **A product of log-concave functions is log-concave.**

This is the closure property the analysis of Gaussian-restricted densities needs: if `f`
is log-concave and `γ` is the Gaussian weight, then `f · γ` is log-concave. -/
theorem LogConcaveOn.mul {s : Set E} {f g : E → ℝ} (hf : LogConcaveOn s f)
    (hg : LogConcaveOn s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) :
    LogConcaveOn s (f * g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  have hz : a • x + b • y ∈ s := hf.1 hx hy ha hb hab
  simp only [Pi.mul_apply]
  rw [Real.mul_rpow (hf₀ hx) (hg₀ hx), Real.mul_rpow (hf₀ hy) (hg₀ hy)]
  calc f x ^ a * g x ^ a * (f y ^ b * g y ^ b)
      = f x ^ a * f y ^ b * (g x ^ a * g y ^ b) := by ring
    _ ≤ f (a • x + b • y) * g (a • x + b • y) :=
        mul_le_mul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
          (mul_nonneg (Real.rpow_nonneg (hg₀ hx) _) (Real.rpow_nonneg (hg₀ hy) _)) (hf₀ hz)

/-- A product of log-concave functions is log-concave. -/
theorem IsLogConcave.mul {f g : E → ℝ} (hf : IsLogConcave f) (hg : IsLogConcave g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) : IsLogConcave (f * g) :=
  LogConcaveOn.mul hf hg (fun x _ => hf₀ x) (fun x _ => hg₀ x)

/-- Scaling a log-concave function by a nonnegative constant preserves log-concavity. -/
theorem LogConcaveOn.const_mul {s : Set E} {f : E → ℝ} (hf : LogConcaveOn s f)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) {c : ℝ} (hc : 0 ≤ c) :
    LogConcaveOn s (fun x => c * f x) :=
  LogConcaveOn.mul (logConcaveOn_const hf.1 hc) hf (fun _ _ => hc) hf₀

/-- Scaling a log-concave function by a nonnegative constant preserves log-concavity. -/
theorem IsLogConcave.const_mul {f : E → ℝ} (hf : IsLogConcave f) (hf₀ : ∀ x, 0 ≤ f x)
    {c : ℝ} (hc : 0 ≤ c) : IsLogConcave (fun x => c * f x) :=
  LogConcaveOn.const_mul hf (fun x _ => hf₀ x) hc

/-- The pointwise minimum of two log-concave functions is log-concave. -/
theorem LogConcaveOn.min {s : Set E} {f g : E → ℝ} (hf : LogConcaveOn s f)
    (hg : LogConcaveOn s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) :
    LogConcaveOn s (fun x => min (f x) (g x)) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [le_min_iff]
  refine ⟨le_trans (mul_le_mul ?_ ?_ ?_ (Real.rpow_nonneg (hf₀ hx) _))
      (hf.2 hx hy ha hb hab),
    le_trans (mul_le_mul ?_ ?_ ?_ (Real.rpow_nonneg (hg₀ hx) _)) (hg.2 hx hy ha hb hab)⟩
  · exact Real.rpow_le_rpow (le_min (hf₀ hx) (hg₀ hx)) (min_le_left _ _) ha
  · exact Real.rpow_le_rpow (le_min (hf₀ hy) (hg₀ hy)) (min_le_left _ _) hb
  · exact Real.rpow_nonneg (le_min (hf₀ hy) (hg₀ hy)) _
  · exact Real.rpow_le_rpow (le_min (hf₀ hx) (hg₀ hx)) (min_le_right _ _) ha
  · exact Real.rpow_le_rpow (le_min (hf₀ hy) (hg₀ hy)) (min_le_right _ _) hb
  · exact Real.rpow_nonneg (le_min (hf₀ hy) (hg₀ hy)) _

/-- A nonnegative real power of a log-concave function is log-concave. -/
theorem LogConcaveOn.rpow {s : Set E} {f : E → ℝ} (hf : LogConcaveOn s f)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) {c : ℝ} (hc : 0 ≤ c) :
    LogConcaveOn s (fun x => f x ^ c) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  have hprod : (0 : ℝ) ≤ f x ^ a * f y ^ b :=
    mul_nonneg (Real.rpow_nonneg (hf₀ hx) _) (Real.rpow_nonneg (hf₀ hy) _)
  calc (f x ^ c) ^ a * (f y ^ c) ^ b
      = (f x ^ a * f y ^ b) ^ c := by
        rw [Real.mul_rpow (Real.rpow_nonneg (hf₀ hx) a) (Real.rpow_nonneg (hf₀ hy) b),
          ← Real.rpow_mul (hf₀ hx), ← Real.rpow_mul (hf₀ hy),
          ← Real.rpow_mul (hf₀ hx), ← Real.rpow_mul (hf₀ hy), mul_comm c a, mul_comm c b]
    _ ≤ f (a • x + b • y) ^ c := Real.rpow_le_rpow hprod (hf.2 hx hy ha hb hab) hc

/-! ### Indicators of convex sets -/

/-- **The indicator of a convex set is log-concave.** This is the running example of the
convex-geometry literature: taking `f = 1_K` says that the ambient measure *restricted to
a convex body* `K` has a log-concave density. -/
theorem isLogConcave_indicator {s : Set E} (hs : Convex ℝ s) :
    IsLogConcave (Set.indicator s (1 : E → ℝ)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · have hz : a • x + b • y ∈ s := hs hx hy ha hb hab
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
    · rcases eq_or_ne b 0 with rfl | hb'
      · have ha1 : a = 1 := by linarith
        subst ha1
        simp [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hy, Real.zero_rpow hb', mul_zero]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · rcases eq_or_ne a 0 with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1
      simp
    · rw [Set.indicator_of_notMem hx, Real.zero_rpow ha', zero_mul]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- Conversely, if the indicator of `s` is log-concave then `s` is convex. -/
theorem convex_of_isLogConcave_indicator {s : Set E}
    (h : IsLogConcave (Set.indicator s (1 : E → ℝ))) : Convex ℝ s := by
  intro x hx y hy a b ha hb hab
  have key := h.geom_le x y ha hb hab
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy] at key
  simp only [Pi.one_apply, Real.one_rpow, one_mul] at key
  by_contra hz
  rw [Set.indicator_of_notMem hz] at key
  linarith

/-- **`Set.indicator s 1` is log-concave exactly when `s` is convex.** -/
theorem isLogConcave_indicator_iff {s : Set E} :
    IsLogConcave (Set.indicator s (1 : E → ℝ)) ↔ Convex ℝ s :=
  ⟨convex_of_isLogConcave_indicator, isLogConcave_indicator⟩

/-! ### Exponentials of concave functions -/

/-- **`exp ∘ g` is log-concave whenever `g` is concave.** This is the constructor that
most log-concave densities are built with. -/
theorem logConcaveOn_exp {s : Set E} {g : E → ℝ} (hg : ConcaveOn ℝ s g) :
    LogConcaveOn s (fun x => Real.exp (g x)) := by
  refine ⟨hg.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hg.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h
  simp only
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  linarith

/-- `exp ∘ g` is log-concave whenever `g` is concave on the whole space. -/
theorem isLogConcave_exp {g : E → ℝ} (hg : ConcaveOn ℝ (Set.univ : Set E) g) :
    IsLogConcave (fun x => Real.exp (g x)) :=
  logConcaveOn_exp hg

/-! ### The logarithmic characterisation -/

/-- **A positive function is log-concave iff its logarithm is concave.**

This is the bridge to Mathlib's `ConcaveOn` API: most log-concavity proofs for strictly
positive densities go through concavity of the logarithm. Positivity is essential — for
functions with zeros the multiplicative form carries strictly more information than
anything `Real.log` can see. -/
theorem logConcaveOn_iff_concaveOn_log {s : Set E} {f : E → ℝ}
    (hf : ∀ ⦃x⦄, x ∈ s → 0 < f x) :
    LogConcaveOn s f ↔ ConcaveOn ℝ s (Real.log ∘ f) := by
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
    have hxa : (0 : ℝ) < f x ^ a := Real.rpow_pos_of_pos (hf hx) _
    have hyb : (0 : ℝ) < f y ^ b := Real.rpow_pos_of_pos (hf hy) _
    have key := Real.log_le_log (mul_pos hxa hyb) (h hx hy ha hb hab)
    rw [Real.log_mul hxa.ne' hyb.ne', Real.log_rpow (hf hx), Real.log_rpow (hf hy)] at key
    simpa only [Function.comp_apply, smul_eq_mul] using key
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
    have hz : a • x + b • y ∈ s := hs hx hy ha hb hab
    have key := h hx hy ha hb hab
    simp only [Function.comp_apply, smul_eq_mul] at key
    rw [Real.rpow_def_of_pos (hf hx), Real.rpow_def_of_pos (hf hy), ← Real.exp_add]
    calc Real.exp (Real.log (f x) * a + Real.log (f y) * b)
        ≤ Real.exp (Real.log (f (a • x + b • y))) := Real.exp_le_exp.mpr (by linarith)
      _ = f (a • x + b • y) := Real.exp_log (hf hz)

/-- A positive function on the whole space is log-concave iff its logarithm is concave. -/
theorem isLogConcave_iff_concaveOn_log {f : E → ℝ} (hf : ∀ x, 0 < f x) :
    IsLogConcave f ↔ ConcaveOn ℝ (Set.univ : Set E) (Real.log ∘ f) :=
  logConcaveOn_iff_concaveOn_log (fun x _ => hf x)

/-! ### Invariance under affine maps -/

/-- The algebraic identity behind affine invariance: the affine map `x ↦ r • x + v`
commutes with convex combinations. -/
theorem smul_add_convex_comb (r : ℝ) (v : E) {a b : ℝ} (hab : a + b = 1) (x y : E) :
    a • (r • x + v) + b • (r • y + v) = r • (a • x + b • y) + v := by
  rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
    mul_comm r a, mul_comm r b, add_add_add_comm, ← add_smul, hab, one_smul]

/-- **Log-concavity is invariant under precomposition with the affine map** `x ↦ r • x + v`;
the domain becomes the preimage of `s`. -/
theorem LogConcaveOn.comp_smul_add {s : Set E} {f : E → ℝ} (hf : LogConcaveOn s f)
    (r : ℝ) (v : E) :
    LogConcaveOn ((fun x => r • x + v) ⁻¹' s) (fun x => f (r • x + v)) := by
  constructor
  · intro x hx y hy a b ha hb hab
    show r • (a • x + b • y) + v ∈ s
    rw [← smul_add_convex_comb r v hab x y]
    exact hf.1 hx hy ha hb hab
  · intro x hx y hy a b ha hb hab
    show f (r • x + v) ^ a * f (r • y + v) ^ b ≤ f (r • (a • x + b • y) + v)
    rw [← smul_add_convex_comb r v hab x y]
    exact hf.2 hx hy ha hb hab

/-- Log-concavity on the whole space is invariant under precomposition with the affine map
`x ↦ r • x + v`. -/
theorem IsLogConcave.comp_smul_add {f : E → ℝ} (hf : IsLogConcave f) (r : ℝ) (v : E) :
    IsLogConcave (fun x => f (r • x + v)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  show f (r • x + v) ^ a * f (r • y + v) ^ b ≤ f (r • (a • x + b • y) + v)
  rw [← smul_add_convex_comb r v hab x y]
  exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

/-! ### Gaussian densities -/

section Gaussian

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The squared norm is convex. -/
theorem convexOn_univ_norm_sq : ConvexOn ℝ (Set.univ : Set F) (fun x : F => ‖x‖ ^ 2) :=
  convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2

/-- **The Gaussian density `γ(x) = e^{−‖x‖²/(2σ²)}` is log-concave.**

No hypothesis on `σ` is needed: at `σ = 0` the exponent is `_ / 0 = 0`, so the function is
the constant `1`, which is log-concave. -/
theorem isLogConcave_gaussian (σ : ℝ) :
    IsLogConcave (fun x : F => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · have h : (fun x : F => Real.exp (-‖x‖ ^ 2 / (2 * (0 : ℝ) ^ 2))) = fun _ => (1 : ℝ) := by
      funext x
      norm_num
    rw [h]
    exact isLogConcave_const zero_le_one
  · have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity
    have h1 : ConvexOn ℝ (Set.univ : Set F) (fun x : F => (2 * σ ^ 2)⁻¹ * ‖x‖ ^ 2) := by
      simpa only [smul_eq_mul] using convexOn_univ_norm_sq.smul (le_of_lt (inv_pos.mpr hσ2))
    have heq : (fun x : F => -‖x‖ ^ 2 / (2 * σ ^ 2))
        = -(fun x : F => (2 * σ ^ 2)⁻¹ * ‖x‖ ^ 2) := by
      funext x
      simp only [Pi.neg_apply]
      ring
    have h2 : ConcaveOn ℝ (Set.univ : Set F) (fun x : F => -‖x‖ ^ 2 / (2 * σ ^ 2)) := by
      rw [heq]
      exact h1.neg
    exact isLogConcave_exp h2

end Gaussian

end Arlib
