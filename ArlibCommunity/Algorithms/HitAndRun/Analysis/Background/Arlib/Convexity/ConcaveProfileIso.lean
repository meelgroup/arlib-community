/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.OneDimIsoperimetry
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.NeedleProfile
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.BrascampLieb1D

/-!
# `(1d-2)` for a *concave* needle profile

Cousins–Vempala state the one-dimensional inequality `(1d-2)`
(`1409.6011/vol3_journal.tex:501`) for a needle profile `ℓ ^ (n−1)` with `ℓ` **affine** —
"a nonnegative linear function `l : [0,1] → ℝ₊`" (`vol3_journal.tex:498`).  This
repository's localization machinery (`Arlib.Convexity.LocalizationAssembly`,
`Arlib.Convexity.LocalizationAffine`, `Arlib.Convexity.LocalizationTransverse`) delivers a
profile `W` that is only known to satisfy "`W ^ (1/m)` concave", and
`Arlib.exists_convex_slice_profile_not_affine` **refutes** the concave-to-affine upgrade.
This file restates and proves `(1d-2)` with `ℓ` merely **concave**, so that the two halves
can be wired together without that (false) upgrade.

## The distinction evaporates

The concave-vs-affine question has a one-line answer for `(1d-2)`, recorded here as
`Arlib.logConcaveOn_concaveProfile_mul`:

> a nonnegative concave `ℓ` is log-concave (`Arlib.logConcaveOn_of_concaveOn`), hence so is
> `ℓ ^ k` (`Arlib.logConcaveOn_pow_of_concaveOn`), hence so is `ℓ ^ k · g` for log-concave
> `g` (`Arlib.LogConcaveOn.mul`).

`Arlib.oneDim_isoperimetry` — the target of `Arlib.Convexity.OneDimIsoperimetry` — is
stated for a *single* log-concave weight `w` with no profile factor at all, so
`(1d-2)` for a concave profile is that theorem applied to `w = ℓ ^ k · g`.  **Affineness of
`ℓ` is never used**, and neither is `k = n − 1`; the profile enters only through the
log-concavity of the product.  Nothing degenerates when `ℓ` has zeros: a nonnegative
concave function on an interval that vanishes at an interior point is identically zero,
and in every case `Arlib.logConcaveOn_of_concaveOn` goes through the weighted AM–GM
inequality, which is insensitive to zeros (`0 ^ c = 0` for `c > 0` and `0 ^ 0 = 1`).

## Main results

* `Arlib.logConcaveOn_concaveProfile_mul` — **the bridge.**  `ℓ ^ k · g` is log-concave for
  `ℓ ≥ 0` concave and `g ≥ 0` log-concave.
* `Arlib.oneDim_isoperimetry_concaveProfile` — **`(1d-2)` for a concave profile**, with the
  sample-point coefficient `ℓ z ^ k · g z / ∫ ℓ ^ k g` of `Arlib.oneDim_isoperimetry`.
* `Arlib.oneDim_isoperimetry_concaveRoot` — the same inequality for a profile `W ≥ 0`
  presented as in the localization output, i.e. with `W ^ (1/m)` concave rather than with a
  factored `ℓ ^ m`.
* `Arlib.oneDim_isoperimetry_variance` — `Arlib.oneDim_isoperimetry_isotropic` with the
  second-moment bound `∫ (t − c)² w ≤ s² ∫ w` at an arbitrary scale `s > 0`, giving the
  coefficient `1 / (2√3 · s)`.  The hypothesis `∫ w > 0` of the isotropic form is dropped:
  at total mass `0` both sides vanish.
* `Arlib.isLogConcave_gaussian_shifted_real` — the one-dimensional Gaussian
  `t ↦ exp(−(t − t₀)²/(2σ²))` is log-concave.
* `Arlib.oneDim_isoperimetry_gaussianFactor` — **the form `Arlib.gaussianRestricted_isoperimetry`
  wants for its `h1d2` binder**, with the honest constant `1/(2√3)` in place of the paper's
  `ln 2` (see below).
* `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional` — **the same with no residual
  binder**, the point `c` and the variance bound supplied by `Arlib.brascampLieb_oneDim`.
* `Arlib.oneDim_isoperimetry_gaussian_concaveProfile` — `(1d-2)` for a concave profile
  against a Gaussian, the two halves combined.
* `Arlib.concaveOn_one_sub_sq`, `Arlib.one_sub_sq_not_affine`,
  `Arlib.oneDim_isoperimetry_concaveProfile_witness`,
  `Arlib.oneDim_isoperimetry_gaussian_concaveProfile_witness` — non-vacuity, with a profile
  that is **genuinely concave and not affine** (`ℓ t = 1 − t²` on `[-1,1]`, which is also a
  case where `ℓ` vanishes, at the two endpoints).

## Relation to `Arlib.Convexity.SharpIsoperimetry`

`Arlib.gaussianRestricted_isoperimetry` carries a binder

```
h1d2 : ∀ (F : ℝ → ℝ) (t₀ α β u v : ℝ), α ≤ u → u ≤ v → v ≤ β →
  (∀ t ∈ Icc α β, 0 ≤ F t) → LogConcaveOn (Icc α β) F →
  IntervalIntegrable (fun t => F t * exp (-(t - t₀)^2 / (2σ²))) volume α β →
  ln 2 / σ * (v - u) * (∫_α^u F·γ) * (∫_v^β F·γ) ≤ (∫_α^β F·γ) * (∫_u^v F·γ)
```

Two facts about it, both stated plainly.

**(a) The binder is already concave-profile-compatible.**  It quantifies over a bare
log-concave `F`, with no profile factor; the profile enters at the call site, where
`Arlib.gaussianRestricted_isoperimetry` builds `F = K · ℓ^(n−1) · (f ∘ needle)` and proves it
log-concave with exactly the bridge above (`SharpIsoperimetry.lean:476–483`).  So for
`(1d-2)` — unlike `(1d-1)`, whose binder `h1d1` does mention `∃ c₀ c₁, ∀ t, l t = c₀ + c₁ t`
— the affine restriction is *not* in the way, and
`Arlib.oneDim_isoperimetry_gaussian_concaveProfile` is exactly the concave-profile call.

**(b) It is not `exact`-compatible as printed, for two reasons — one of substance, one of
missing input.**

*The constant.*  What is proved here is `1/(2√3) ≈ 0.2887`, not `ln 2 ≈ 0.6931`; the two
lossy steps are identified in the docstring of `Arlib.oneDim_isoperimetry_isotropic` and are
slack in this argument, not an error in the paper.  `Arlib.Convexity.SharpIsoperimetry`'s own
docstring already anticipates the substitution: `h1d2` reinstantiated with `1/(2√3)` for
`ln 2`, and the separation hypothesis's metric branch with `2√3·d` for `d/ln 2`.  The proof
of `Arlib.gaussianRestricted_isoperimetry` is insensitive to the value.

*One extra binder: the second moment — since closed.*
`Arlib.oneDim_isoperimetry_gaussianFactor` carries a hypothesis `h1d2` does not —
`∫_α^β (t − c)² F·γ ≤ σ² ∫_α^β F·γ` for some `c ∈ [α,β]`.  That is not an additional
assumption on the mathematics but a *theorem* about the data `h1d2` already quantifies over,
and it is exactly the step Cousins–Vempala cite at `vol3_journal.tex:506`.  It was a binder
only because the repository's `Arlib.brascampLieb`
(`Arlib/Convexity/GaussianCooling/Variance.lean:693`) is the needle-specific special case
`J₂J₀ − J₁² ≤ (σ²/x)J₀²` for the exponential family `s(x,·)`, with no log-concave factor.

`Arlib.brascampLieb_oneDim` (`Arlib/Convexity/BrascampLieb1D.lean`) now proves the general
form, so `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional` below is `h1d2` **verbatim
at the constant `1/(2√3)`**, with no residual binder.  Its `c` is the barycentre — the
optimal choice, since `c ↦ ∫ (t − c)² w` is minimised there — so nothing is lost.  The only
remaining mismatch with the printed `h1d2` is the constant, item (b)'s first paragraph, which
the proof of `Arlib.gaussianRestricted_isoperimetry` is insensitive to.

## No rate claim

Nothing here says, or implies, that any algorithm runs in polynomial time.  This file
proves an isoperimetric inequality with an explicit absolute constant; it contains no
mixing, conductance, or complexity statement.

## References

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian
Volume*, §3 (`1409.6011/vol3_journal.tex:404–508`).

Kannan, Lovász and Simonovits, *Isoperimetric problems for convex bodies and a localization
lemma*, Discrete Comput. Geom. **13** (1995), Theorem 5.1.
-/

namespace Arlib

open MeasureTheory Set

/-! ### The bridge: a concave profile times a log-concave weight is log-concave -/

section Bridge

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **A nonnegative concave profile raised to a natural power, times a nonnegative
log-concave function, is log-concave.**

This is the whole content of the concave-vs-affine question for `(1d-2)`: the profile enters
the one-dimensional inequality only through the log-concavity of the product, and
log-concavity of `ℓ ^ k` needs `ℓ` merely concave and nonnegative
(`Arlib.logConcaveOn_pow_of_concaveOn`), never affine.

Zeros of `ℓ` are harmless.  On an interval a nonnegative concave function vanishing at an
interior point is identically zero, and in any case
`Arlib.logConcaveOn_of_concaveOn` argues through weighted AM–GM, for which `0 ^ c = 0`
(`c > 0`) and `0 ^ 0 = 1` are the right conventions. -/
theorem logConcaveOn_concaveProfile_mul {s : Set E} {ℓ g : E → ℝ}
    (hℓ : ConcaveOn ℝ s ℓ) (hℓ₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ ℓ x)
    (hg : LogConcaveOn s g) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (k : ℕ) :
    LogConcaveOn s (fun x => ℓ x ^ k * g x) :=
  LogConcaveOn.mul (logConcaveOn_pow_of_concaveOn hℓ hℓ₀ k) hg
    (fun _ hx => pow_nonneg (hℓ₀ hx) k) hg₀

/-- Log-concavity on `s` only sees the values on `s`, so it transfers along any function
that agrees with a log-concave one there.  (Convexity of `s` is what makes the midpoint
`a • x + b • y` land in `s`, where the two functions still agree.) -/
theorem LogConcaveOn.congr_on {s : Set E} {f h : E → ℝ} (hf : LogConcaveOn s f)
    (hfh : ∀ ⦃x⦄, x ∈ s → f x = h x) : LogConcaveOn s h := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  rw [← hfh hx, ← hfh hy, ← hfh (hf.1 hx hy ha hb hab)]
  exact hf.2 hx hy ha hb hab

end Bridge

/-! ### `(1d-2)` for a concave profile -/

section ConcaveProfile

variable {a b : ℝ} {ℓ g : ℝ → ℝ} {k : ℕ}

/-- **Cousins–Vempala inequality `(1d-2)` for a *concave* needle profile.**

For `ℓ ≥ 0` concave on `[a,b]`, `g ≥ 0` log-concave on `[a,b]`, any `k : ℕ`, any sample point
`z ∈ [a,b]` and `a ≤ u ≤ v ≤ b`,

  `ℓ z ^ k · g z · (v − u) · (∫_a^u ℓ^k g) · (∫_v^b ℓ^k g)
      ≤ (∫_a^b ℓ^k g) ² · (∫_u^v ℓ^k g)`,

i.e. the paper's `∫_a^b ω · ∫_u^v ω ≥ c‖u − v‖ · ∫_a^u ω · ∫_v^b ω` for the needle weight
`ω = ℓ^k g`, with coefficient `c = ℓ z ^ k g z / ∫_a^b ℓ^k g`.

The paper takes `ℓ` affine and `k = n − 1`; **neither is used**.  The proof is
`Arlib.oneDim_isoperimetry` applied to the single weight `w = ℓ ^ k · g`, which is
log-concave by `Arlib.logConcaveOn_concaveProfile_mul`. -/
theorem oneDim_isoperimetry_concaveProfile
    (hℓ : ConcaveOn ℝ (Set.Icc a b) ℓ) (hℓ₀ : ∀ t ∈ Set.Icc a b, 0 ≤ ℓ t)
    (hg : LogConcaveOn (Set.Icc a b) g) (hg₀ : ∀ t ∈ Set.Icc a b, 0 ≤ g t)
    (hint : IntervalIntegrable (fun t => ℓ t ^ k * g t) volume a b)
    {z u v : ℝ} (hz : z ∈ Set.Icc a b) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    ℓ z ^ k * g z * (v - u) *
        ((∫ t in a..u, ℓ t ^ k * g t) * (∫ t in v..b, ℓ t ^ k * g t))
      ≤ (∫ t in a..b, ℓ t ^ k * g t) ^ 2 * (∫ t in u..v, ℓ t ^ k * g t) :=
  oneDim_isoperimetry (w := fun t => ℓ t ^ k * g t)
    (logConcaveOn_concaveProfile_mul hℓ (fun _ ht => hℓ₀ _ ht) hg (fun _ ht => hg₀ _ ht) k)
    (fun t ht => mul_nonneg (pow_nonneg (hℓ₀ t ht) k) (hg₀ t ht)) hint hz hau huv hvb

/-- **`(1d-2)` in the shape the Localization Lemma hands it over.**

`Arlib.needleIntegral_eq_zero_and_ge` and its relatives
(`Arlib.Convexity.LocalizationAssembly`) deliver the needle profile as a single function
`W ≥ 0` together with `ConcaveOn ℝ · (fun t => W t ^ (1/m))`
(`Arlib.concaveOn_limit_normalised_slice_profile`, with `m = n − 1`), *not* as a factored
`ℓ ^ m`.  This is the same inequality as `Arlib.oneDim_isoperimetry_concaveProfile` presented
against that data: for `a ≤ u ≤ v ≤ b` and `z ∈ [a,b]`,

  `W z · g z · (v − u) · (∫_a^u W g) · (∫_v^b W g) ≤ (∫_a^b W g)² · (∫_u^v W g)`.

The two presentations are interchangeable because `W = (W^{1/m})^m` wherever `W ≥ 0`; that
identity is applied to the *log-concavity* of the weight (`Arlib.LogConcaveOn.congr_on`)
rather than to the four integrals, so the statement above is literally about `W · g`. -/
theorem oneDim_isoperimetry_concaveRoot {W : ℝ → ℝ} {m : ℕ} (hm : m ≠ 0)
    (hW₀ : ∀ t ∈ Set.Icc a b, 0 ≤ W t)
    (hWc : ConcaveOn ℝ (Set.Icc a b) (fun t => W t ^ (1 / (m : ℝ))))
    (hg : LogConcaveOn (Set.Icc a b) g) (hg₀ : ∀ t ∈ Set.Icc a b, 0 ≤ g t)
    (hint : IntervalIntegrable (fun t => W t * g t) volume a b)
    {z u v : ℝ} (hz : z ∈ Set.Icc a b) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    W z * g z * (v - u) *
        ((∫ t in a..u, W t * g t) * (∫ t in v..b, W t * g t))
      ≤ (∫ t in a..b, W t * g t) ^ 2 * (∫ t in u..v, W t * g t) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hlm : ∀ t ∈ Set.Icc a b, (W t ^ (1 / (m : ℝ))) ^ m * g t = W t * g t := by
    intro t ht
    rw [← Real.rpow_natCast (W t ^ (1 / (m : ℝ))) m, ← Real.rpow_mul (hW₀ t ht), one_div,
      inv_mul_cancel₀ hmR, Real.rpow_one]
  have hlc : LogConcaveOn (Set.Icc a b) (fun t => W t * g t) :=
    (logConcaveOn_concaveProfile_mul hWc
      (fun t ht => Real.rpow_nonneg (hW₀ t ht) _) hg (fun t ht => hg₀ t ht) m).congr_on
      (fun t ht => hlm t ht)
  exact oneDim_isoperimetry hlc (fun t ht => mul_nonneg (hW₀ t ht) (hg₀ t ht)) hint hz hau
    huv hvb

end ConcaveProfile

/-! ### The coefficient from a second moment at an arbitrary scale -/

section Variance

/-- **`Arlib.oneDim_isoperimetry_isotropic` at an arbitrary scale.**

Let `w ≥ 0` be log-concave on `[a,b]` and suppose its second moment about some `c ∈ [a,b]`
is at most `s²` times its total mass: `∫_a^b (t − c)² w ≤ s² ∫_a^b w`.  Then for
`a ≤ u ≤ v ≤ b`,

  `(1 / (2√3 · s)) · (v − u) · (∫_a^u w) · (∫_v^b w) ≤ (∫_a^b w) · (∫_u^v w)`,

i.e. `π(S₃) ≥ (1/(2√3 s)) · d(S₁,S₂) · π(S₁) · π(S₂)` for `π = w / ∫ w`.  At `s = 1` this
is exactly `Arlib.oneDim_isoperimetry_isotropic`; the general `s` is what the needle needs,
where Brascamp–Lieb bounds the second moment by `σ²` rather than by `1`
(`vol3_journal.tex:506`).  Because the coefficient scales as `1/s`, this is the *same*
inequality read in the units in which the needle density is isotropic — no new analysis.

The hypothesis `0 < ∫_a^b w` of `Arlib.oneDim_isoperimetry_isotropic` is not needed: if the
total mass vanishes then, `w` being nonnegative, all four integrals vanish and both sides
are `0`.

The proof is the one in `Arlib.oneDim_isoperimetry_isotropic`, run with the window height
`K = Z / (2√3 s)`: Hensley's bound `Arlib.cube_le_sq_mul_moment` says a weight capped below
`K` would force `Z³ ≤ 12 K² s² Z = Z³` strictly, so `w` comes arbitrarily close to `K`
somewhere, and `Arlib.oneDim_isoperimetry` at such a point is the claim in the limit. -/
theorem oneDim_isoperimetry_variance {a b c s : ℝ} {w : ℝ → ℝ} (hs : 0 < s)
    (hw : LogConcaveOn (Set.Icc a b) w) (hw0 : ∀ t ∈ Set.Icc a b, 0 ≤ w t)
    (hint : IntervalIntegrable w volume a b) (hc : c ∈ Set.Icc a b)
    (hvar : (∫ t in a..b, (t - c) ^ 2 * w t) ≤ s ^ 2 * ∫ t in a..b, w t)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    1 / (2 * Real.sqrt 3 * s) * ((v - u) * ((∫ t in a..u, w t) * (∫ t in v..b, w t)))
      ≤ (∫ t in a..b, w t) * (∫ t in u..v, w t) := by
  have hsne : s ≠ 0 := hs.ne'
  have hab : a ≤ b := hau.trans (huv.trans hvb)
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set Z : ℝ := ∫ t in a..b, w t with hZdef
  set L : ℝ := ∫ t in a..u, w t with hLdef
  set R : ℝ := ∫ t in v..b, w t with hRdef
  set Mid : ℝ := ∫ t in u..v, w t with hMdef
  have hL0 : 0 ≤ L :=
    intervalIntegral.integral_nonneg hau fun t ht => hw0 t ⟨ht.1, by linarith [ht.2]⟩
  have hM0 : 0 ≤ Mid :=
    intervalIntegral.integral_nonneg huv fun t ht =>
      hw0 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hR0 : 0 ≤ R :=
    intervalIntegral.integral_nonneg hvb fun t ht => hw0 t ⟨by linarith [ht.1], ht.2⟩
  have hZ0 : 0 ≤ Z := intervalIntegral.integral_nonneg hab fun t ht => hw0 t ht
  have hsum : L + Mid + R = Z := by
    have h1 : L + Mid = ∫ t in a..v, w t :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl hau (huv.trans hvb))
        (intervalIntegrable_of_subinterval hint hau huv hvb)
    have h2 : (∫ t in a..v, w t) + R = Z :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_subinterval hint le_rfl (hau.trans huv) hvb)
        (intervalIntegrable_of_subinterval hint (hau.trans huv) hvb le_rfl)
    rw [h1]; exact h2
  rcases eq_or_lt_of_le hZ0 with hZzero | hZpos
  · -- total mass `0`: every integral vanishes and both sides are `0`
    have hLz : L = 0 := by linarith
    have hRz : R = 0 := by linarith
    have hMz : Mid = 0 := by linarith
    rw [hLz, hRz, hMz, ← hZzero]
    norm_num
  set K : ℝ := Z / (2 * Real.sqrt 3 * s) with hKdef
  set X : ℝ := (v - u) * (L * R) with hXdef
  have hK0 : 0 < K := div_pos hZpos (by positivity)
  have hX0 : 0 ≤ X := mul_nonneg (by linarith) (mul_nonneg hL0 hR0)
  have hden : (2 * Real.sqrt 3 * s) ^ 2 = 12 * s ^ 2 := by
    rw [mul_pow, mul_pow, hs3sq]; ring
  have hKsq : 12 * K ^ 2 * s ^ 2 = Z ^ 2 := by
    rw [hKdef, div_pow, hden]; field_simp
  -- Hensley forces `w` to come arbitrarily close to `K` somewhere on `[a,b]`
  have hex : ∀ ε : ℝ, 0 < ε → ∃ z ∈ Set.Icc a b, K - ε < w z := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    rcases le_or_gt (K - ε) 0 with hMle | hMpos
    · have hZle0 : Z ≤ 0 := by
        have h := intervalIntegral.integral_mono_on hab hint
          (intervalIntegrable_const (c := (0 : ℝ))) fun t ht => (hcon t ht).trans hMle
        simpa using h
      linarith
    · have hH := cube_le_sq_mul_moment (M := K - ε) hMpos hw0 hcon hint hc
      have hVZ : 12 * (K - ε) ^ 2 * (∫ t in a..b, (t - c) ^ 2 * w t)
          ≤ 12 * (K - ε) ^ 2 * (s ^ 2 * Z) := mul_le_mul_of_nonneg_left hvar (by positivity)
      have hlt : 12 * (K - ε) ^ 2 * s ^ 2 < 12 * K ^ 2 * s ^ 2 := by
        have h1 : (K - ε) ^ 2 < K ^ 2 := by nlinarith
        have hsq : (0 : ℝ) < s ^ 2 := by positivity
        nlinarith [h1, hsq]
      have hself : Z ^ 3 < Z ^ 3 :=
        calc Z ^ 3 ≤ 12 * (K - ε) ^ 2 * (∫ t in a..b, (t - c) ^ 2 * w t) := hH
          _ ≤ 12 * (K - ε) ^ 2 * (s ^ 2 * Z) := hVZ
          _ = (12 * (K - ε) ^ 2 * s ^ 2) * Z := by ring
          _ < (12 * K ^ 2 * s ^ 2) * Z := mul_lt_mul_of_pos_right hlt hZpos
          _ = Z ^ 2 * Z := by rw [hKsq]
          _ = Z ^ 3 := by ring
      exact lt_irrefl _ hself
  -- transport `Arlib.oneDim_isoperimetry` to those points, then let `ε → 0`
  have hmain : ∀ z ∈ Set.Icc a b, w z * X ≤ Z ^ 2 * Mid := by
    intro z hz
    have h := oneDim_isoperimetry hw hw0 hint hz hau huv hvb
    calc w z * X = w z * (v - u) * (L * R) := by rw [hXdef]; ring
      _ ≤ _ := h
  have hKX : K * X ≤ Z ^ 2 * Mid := by
    by_contra hcon
    push Not at hcon
    set δ : ℝ := K * X - Z ^ 2 * Mid with hδdef
    have hδ : 0 < δ := by rw [hδdef]; linarith
    obtain ⟨z, hz, hzw⟩ := hex (δ / (2 * (X + 1))) (by positivity)
    have h1 := hmain z hz
    have h2 : (K - δ / (2 * (X + 1))) * X ≤ w z * X :=
      mul_le_mul_of_nonneg_right hzw.le hX0
    have h3 : δ / (2 * (X + 1)) * X ≤ δ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hδ, hX0]
    nlinarith [h1, h2, h3, hδ]
  refine le_of_mul_le_mul_left ?_ hZpos
  calc Z * (1 / (2 * Real.sqrt 3 * s) * X) = K * X := by rw [hKdef]; ring
    _ ≤ Z ^ 2 * Mid := hKX
    _ = Z * (Z * Mid) := by ring

end Variance

/-! ### The form `Arlib.gaussianRestricted_isoperimetry` consumes -/

section GaussianFactor

/-- **The shifted one-dimensional Gaussian is log-concave.**

`Arlib.isLogConcave_gaussian` for `F = ℝ`, precomposed with the translation `t ↦ t − t₀`
(`Arlib.IsLogConcave.comp_smul_add`).  No hypothesis on `σ`: at `σ = 0` the exponent is
`_ / 0 = 0` and the function is the constant `1`. -/
theorem isLogConcave_gaussian_shifted_real (t₀ σ : ℝ) :
    IsLogConcave (fun t : ℝ => Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) := by
  have h := (isLogConcave_gaussian (F := ℝ) σ).comp_smul_add 1 (-t₀)
  have he : (fun t : ℝ => Real.exp (-‖(1 : ℝ) • t + -t₀‖ ^ 2 / (2 * σ ^ 2)))
      = fun t : ℝ => Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) := by
    funext t
    simp only [one_smul, Real.norm_eq_abs, sq_abs, ← sub_eq_add_neg]
  rwa [he] at h

/-- **`(1d-2)` in exactly the shape `Arlib.gaussianRestricted_isoperimetry`'s `h1d2` binder
asks for**, with the honest constant.

For a nonnegative log-concave `F` on `[α,β]` and the Gaussian factor
`γ(t) = exp(−(t − t₀)²/(2σ²))`, writing `ω = F·γ`, and for `α ≤ u ≤ v ≤ β`,

  `(1/(2√3))/σ · (v − u) · (∫_α^u ω) · (∫_v^β ω) ≤ (∫_α^β ω) · (∫_u^v ω)`.

**Two differences from the printed `h1d2`, both unavoidable.**

*The constant.*  Cousins–Vempala's `\iso` is `ln 2 ≈ 0.6931` (`vol3_journal.tex:65`); what is
proved here is `1/(2√3) ≈ 0.2887`.  The gap is slack in two steps of
`Arlib.oneDim_isoperimetry_isotropic`, identified in that theorem's docstring, not an error in
the paper.  `Arlib.Convexity.SharpIsoperimetry`'s own docstring already anticipates the
substitution: `h1d2` reinstantiated with `1/(2√3)` for `ln 2`, and the separation
hypothesis's metric branch with `2√3·d` for `d/ln 2`.

*The extra binder.*  `h1d2` as printed has no second-moment hypothesis.  `hvar` is not an
additional assumption on the mathematics — it is a *theorem* about the data already
quantified over: `F·γ` has density `exp(−V)` with `V'' ≥ 1/σ²` (because `−log F` is convex),
so Brascamp–Lieb bounds its variance by `σ²`, which is precisely the step
Cousins–Vempala take at `vol3_journal.tex:506`.  It appears as a binder only because that
form of Brascamp–Lieb — for `log-concave × Gaussian` — is not in this repository;
`Arlib.brascampLieb` (`Arlib/Convexity/GaussianCooling/Variance.lean:693`) is the
needle-specific case with no log-concave factor and does not apply here.  Discharging `hvar`
turns this theorem into `h1d2` verbatim at the constant `1/(2√3)`. -/
theorem oneDim_isoperimetry_gaussianFactor {σ : ℝ} (hσ : 0 < σ) (F : ℝ → ℝ)
    (t₀ α β u v : ℝ) (hau : α ≤ u) (huv : u ≤ v) (hvβ : v ≤ β)
    (hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t) (hFc : LogConcaveOn (Set.Icc α β) F)
    (hint : IntervalIntegrable
      (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β)
    {c : ℝ} (hc : c ∈ Set.Icc α β)
    (hvar : (∫ t in α..β, (t - c) ^ 2 * (F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      ≤ σ ^ 2 * ∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) :
    1 / (2 * Real.sqrt 3) / σ * (v - u) *
        ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      ≤ (∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in u..v, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) := by
  have hlc : LogConcaveOn (Set.Icc α β)
      (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) :=
    LogConcaveOn.mul hFc
      ((isLogConcave_gaussian_shifted_real t₀ σ).logConcaveOn (convex_Icc α β)) hF0
      (fun _ _ => (Real.exp_pos _).le)
  have h := oneDim_isoperimetry_variance (s := σ) (c := c) hσ hlc
    (fun t ht => mul_nonneg (hF0 t ht) (Real.exp_pos _).le) hint hc hvar hau huv hvβ
  calc 1 / (2 * Real.sqrt 3) / σ * (v - u) *
        ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      = 1 / (2 * Real.sqrt 3 * σ) * ((v - u) *
          ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))) := by
        rw [div_div]; ring
    _ ≤ _ := h

/-- **`(1d-2)` for a concave profile against a Gaussian.**

`Arlib.oneDim_isoperimetry_gaussianFactor` at `F = ℓ ^ k · f`: the needle weight the
Localization Lemma actually produces, with `ℓ ≥ 0` **concave** (not affine) and `f` the
log-concave restriction the Gaussian is cut by.  This is the call
`Arlib.gaussianRestricted_isoperimetry` makes at `SharpIsoperimetry.lean:506`, with the
affine `ℓ` of that file replaced by a concave one — the only change needed on the `(1d-2)`
side to accept the concave profile of `Arlib.Convexity.LocalizationAssembly`. -/
theorem oneDim_isoperimetry_gaussian_concaveProfile {σ : ℝ} (hσ : 0 < σ) {ℓ f : ℝ → ℝ}
    {k : ℕ} {t₀ α β u v : ℝ} (hau : α ≤ u) (huv : u ≤ v) (hvβ : v ≤ β)
    (hℓ : ConcaveOn ℝ (Set.Icc α β) ℓ) (hℓ₀ : ∀ t ∈ Set.Icc α β, 0 ≤ ℓ t)
    (hf : LogConcaveOn (Set.Icc α β) f) (hf₀ : ∀ t ∈ Set.Icc α β, 0 ≤ f t)
    (hint : IntervalIntegrable
      (fun t => ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β)
    {c : ℝ} (hc : c ∈ Set.Icc α β)
    (hvar : (∫ t in α..β,
        (t - c) ^ 2 * (ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      ≤ σ ^ 2 * ∫ t in α..β, ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) :
    1 / (2 * Real.sqrt 3) / σ * (v - u) *
        ((∫ t in α..u, ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in v..β, ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      ≤ (∫ t in α..β, ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in u..v, ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) :=
  oneDim_isoperimetry_gaussianFactor hσ (fun t => ℓ t ^ k * f t) t₀ α β u v hau huv hvβ
    (fun t ht => mul_nonneg (pow_nonneg (hℓ₀ t ht) k) (hf₀ t ht))
    (logConcaveOn_concaveProfile_mul hℓ (fun _ ht => hℓ₀ _ ht) hf (fun _ ht => hf₀ _ ht) k)
    hint hc hvar

end GaussianFactor

/-! ### Non-vacuity, with a profile that is concave but **not** affine

Everything above would be worthless if "concave, nonnegative and not affine" were an empty
description of a profile, or if the hypotheses could not be met with both sides strictly
positive.  The witness is `ℓ t = 1 − t²` on `[-1,1]`: concave, nonnegative, vanishing at
both endpoints (so the degenerate case `ℓ = 0` is exercised), and demonstrably not affine on
`[-1,1]` — exactly the situation `Arlib.exists_convex_slice_profile_not_affine` says the
Localization Lemma can produce and the paper's affine statement of `(1d-2)` cannot accept. -/

section Witness

/-- `t ↦ 1 − t²` is concave on every convex set. -/
theorem concaveOn_one_sub_sq {s : Set ℝ} (hs : Convex ℝ s) :
    ConcaveOn ℝ s (fun t => 1 - t ^ 2) := by
  refine ⟨hs, fun x _ y _ a b ha hb hab => ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [smul_eq_mul]
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]

/-- **The witness profile is not affine.**  `1 − t²` is not of the form `c₀ + c₁t` on
`[-1,1]`: the three points `t = 0, 1, −1` force `c₀ = 1` and then `c₁ = −1` and `c₁ = 1`.

This is what separates the statement proved in this file from the one Cousins–Vempala print:
their `(1d-2)` is stated for `ℓ` affine (`vol3_journal.tex:498`), and no affine `ℓ` can
represent this profile. -/
theorem one_sub_sq_not_affine :
    ¬ ∃ c₀ c₁ : ℝ, ∀ t ∈ Set.Icc (-1 : ℝ) 1, 1 - t ^ 2 = c₀ + c₁ * t := by
  rintro ⟨c₀, c₁, h⟩
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  norm_num at h0 h1 h2
  linarith

/-- **Non-vacuity of `Arlib.oneDim_isoperimetry_concaveProfile`.**

Every hypothesis is satisfiable simultaneously with a strictly positive left-hand side, by
data in which the profile `ℓ` is genuinely concave and **not affine**: `ℓ t = 1 − t²` on
`[-1,1]` (so `ℓ` also *vanishes*, at both endpoints — the degenerate case), `k = 2`,
`g ≡ 1`, sample point `z = 0`, cut at `u = −1/2`, `v = 1/2`.  So the theorem is not the
vacuous `0 ≤ something`, and its concave hypothesis is strictly weaker than the affine one
the paper states: here is data satisfying the former for which no affine `ℓ` exists. -/
theorem oneDim_isoperimetry_concaveProfile_witness :
    ∃ (ℓ g : ℝ → ℝ) (k : ℕ) (a b z u v : ℝ),
      ConcaveOn ℝ (Set.Icc a b) ℓ ∧ (∀ t ∈ Set.Icc a b, 0 ≤ ℓ t) ∧
        LogConcaveOn (Set.Icc a b) g ∧ (∀ t ∈ Set.Icc a b, 0 ≤ g t) ∧
        IntervalIntegrable (fun t => ℓ t ^ k * g t) volume a b ∧
        z ∈ Set.Icc a b ∧ a ≤ u ∧ u ≤ v ∧ v ≤ b ∧
        (¬ ∃ c₀ c₁ : ℝ, ∀ t ∈ Set.Icc a b, ℓ t = c₀ + c₁ * t) ∧
        0 < ℓ z ^ k * g z * (v - u) *
          ((∫ t in a..u, ℓ t ^ k * g t) * (∫ t in v..b, ℓ t ^ k * g t)) := by
  have hcont : Continuous (fun t : ℝ => (1 - t ^ 2) ^ 2 * (1 : ℝ)) := by fun_prop
  have hpos : ∀ p q : ℝ, -1 ≤ p → p < q → q ≤ 1 →
      0 < ∫ t in p..q, (1 - t ^ 2) ^ 2 * (1 : ℝ) := by
    intro p q hp hpq hq
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable _ _) (fun x hx => ?_) hpq
    have hx1 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    nlinarith [mul_pos hx1 hx1]
  refine ⟨fun t => 1 - t ^ 2, fun _ => (1 : ℝ), 2, -1, 1, 0, -(1 / 2), 1 / 2,
    concaveOn_one_sub_sq (convex_Icc _ _), fun t ht => by nlinarith [ht.1, ht.2],
    logConcaveOn_const (convex_Icc _ _) zero_le_one, fun _ _ => zero_le_one,
    hcont.intervalIntegrable _ _, ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num,
    by norm_num, one_sub_sq_not_affine, ?_⟩
  have h1 : 0 < ∫ t in (-1 : ℝ)..(-(1 / 2)), (1 - t ^ 2) ^ 2 * (1 : ℝ) :=
    hpos _ _ le_rfl (by norm_num) (by norm_num)
  have h2 : 0 < ∫ t in (1 / 2 : ℝ)..1, (1 - t ^ 2) ^ 2 * (1 : ℝ) :=
    hpos _ _ (by norm_num) (by norm_num) le_rfl
  exact mul_pos (by norm_num) (mul_pos h1 h2)

/-- **Non-vacuity of `Arlib.oneDim_isoperimetry_gaussian_concaveProfile`**, hence of
`Arlib.oneDim_isoperimetry_gaussianFactor` and `Arlib.oneDim_isoperimetry_variance`.

The same non-affine concave profile `ℓ t = 1 − t²` on `[-1,1]` with `k = 2`, against the
standard Gaussian (`σ = 1`, `t₀ = 0`) restricted by `f ≡ 1`, second moment taken about
`c = 0`, cut at `u = −1/2`, `v = 1/2`.  The second-moment hypothesis holds for the crude
reason that `t² ≤ 1` on `[-1,1]`, so no Brascamp–Lieb input is needed *for the witness* —
but it is needed in general, which is exactly why it is a binder.

The left-hand side is strictly positive, so the conclusion is a genuine lower bound and no
two hypotheses of the theorem are in conflict. -/
theorem oneDim_isoperimetry_gaussian_concaveProfile_witness :
    ∃ (ℓ f : ℝ → ℝ) (k : ℕ) (σ t₀ α β c u v : ℝ),
      0 < σ ∧ α ≤ u ∧ u ≤ v ∧ v ≤ β ∧
        ConcaveOn ℝ (Set.Icc α β) ℓ ∧ (∀ t ∈ Set.Icc α β, 0 ≤ ℓ t) ∧
        LogConcaveOn (Set.Icc α β) f ∧ (∀ t ∈ Set.Icc α β, 0 ≤ f t) ∧
        IntervalIntegrable
          (fun t => ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β ∧
        c ∈ Set.Icc α β ∧
        ((∫ t in α..β,
            (t - c) ^ 2 * (ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
          ≤ σ ^ 2 * ∫ t in α..β, ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) ∧
        (¬ ∃ c₀ c₁ : ℝ, ∀ t ∈ Set.Icc α β, ℓ t = c₀ + c₁ * t) ∧
        0 < 1 / (2 * Real.sqrt 3) / σ * (v - u) *
          ((∫ t in α..u, ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in v..β, ℓ t ^ k * f t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) := by
  have hcont : Continuous (fun t : ℝ =>
      (1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2))) := by fun_prop
  have hnn : ∀ t : ℝ,
      (0 : ℝ) ≤ (1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) :=
    fun t => by positivity
  have hpos : ∀ p q : ℝ, -1 ≤ p → p < q → q ≤ 1 →
      0 < ∫ t in p..q, (1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := by
    intro p q hp hpq hq
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable _ _) (fun x hx => ?_) hpq
    have hx1 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hx2 : (0 : ℝ) < Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := Real.exp_pos _
    nlinarith [mul_pos (mul_pos hx1 hx1) hx2]
  refine ⟨fun t => 1 - t ^ 2, fun _ => (1 : ℝ), 2, 1, 0, -1, 1, 0, -(1 / 2), 1 / 2,
    one_pos, by norm_num, by norm_num, by norm_num,
    concaveOn_one_sub_sq (convex_Icc _ _), fun t ht => by nlinarith [ht.1, ht.2],
    logConcaveOn_const (convex_Icc _ _) zero_le_one, fun _ _ => zero_le_one,
    hcont.intervalIntegrable _ _, ⟨by norm_num, by norm_num⟩, ?_,
    one_sub_sq_not_affine, ?_⟩
  · -- the second moment about `c = 0` is at most `σ² = 1` times the mass, since `t² ≤ 1`
    have key : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        (t - 0) ^ 2 * ((1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)))
          ≤ (1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := by
      intro t ht
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht2) (hnn t)]
    calc (∫ t in (-1 : ℝ)..1,
          (t - 0) ^ 2 * ((1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2))))
        ≤ ∫ t in (-1 : ℝ)..1,
            (1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) :=
          intervalIntegral.integral_mono_on (by norm_num)
            (Continuous.intervalIntegrable (by fun_prop) _ _)
            (hcont.intervalIntegrable _ _) key
      _ = (1 : ℝ) ^ 2 * ∫ t in (-1 : ℝ)..1,
            (1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) := by ring
  · have h1 : 0 < ∫ t in (-1 : ℝ)..(-(1 / 2)),
        (1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) :=
      hpos _ _ le_rfl (by norm_num) (by norm_num)
    have h2 : 0 < ∫ t in (1 / 2 : ℝ)..1,
        (1 - t ^ 2) ^ 2 * (1 : ℝ) * Real.exp (-(t - 0) ^ 2 / (2 * (1 : ℝ) ^ 2)) :=
      hpos _ _ (by norm_num) (by norm_num) le_rfl
    have h3 : (0 : ℝ) < 1 / (2 * Real.sqrt 3) / 1 * (1 / 2 - -(1 / 2)) := by
      have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    exact mul_pos h3 (mul_pos h1 h2)

end Witness

/-! ### `(1d-2)` with no residual binder

`oneDim_isoperimetry_gaussianFactor` above carries two hypotheses — a point `c` and the
variance bound at `c` — that Cousins–Vempala obtain from Brascamp–Lieb
(`vol3_journal.tex:407`).  `Arlib.brascampLieb_oneDim` proves exactly that, so the two
compose into a statement whose hypotheses are all about the *data*: `σ > 0`, the interval
order, nonnegativity, log-concavity, and integrability. -/

/-- **`(1d-2)` for a log-concave `F` against a Gaussian, with no residual binder.**
`Arlib.brascampLieb_oneDim` supplies the point `c` and the variance bound that
`oneDim_isoperimetry_gaussianFactor` asks for; `c` is the barycentre, which is the optimal
choice, so nothing is lost by discharging it this way.

The constant is `1/(2√3)/σ`, and the `σ` in the denominator is the one
`Arlib.gaussianRestricted_isoperimetry`'s `d/σ` needs.  Cousins–Vempala state
Brascamp–Lieb for the *standard* Gaussian and read off "variance ≤ 1" only inside their
`σ = 1` reduction; the intrinsic general-`σ` form is `σ²`, which is what is proved here. -/
theorem oneDim_isoperimetry_gaussianFactor_unconditional {σ : ℝ} (hσ : 0 < σ) (F : ℝ → ℝ)
    (t₀ α β u v : ℝ) (hau : α ≤ u) (huv : u ≤ v) (hvβ : v ≤ β)
    (hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t) (hFc : LogConcaveOn (Set.Icc α β) F)
    (hint : IntervalIntegrable
      (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β) :
    1 / (2 * Real.sqrt 3) / σ * (v - u) *
        ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
      ≤ (∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
          (∫ t in u..v, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) := by
  obtain ⟨c, hc, hvar⟩ := brascampLieb_oneDim hσ (hau.trans (huv.trans hvβ)) hF0 hFc hint
  exact oneDim_isoperimetry_gaussianFactor hσ F t₀ α β u v hau huv hvβ hF0 hFc hint hc hvar

end Arlib

/-! ### Axiom audit

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Arlib.logConcaveOn_concaveProfile_mul
#print axioms Arlib.LogConcaveOn.congr_on
#print axioms Arlib.oneDim_isoperimetry_concaveProfile
#print axioms Arlib.oneDim_isoperimetry_concaveRoot
#print axioms Arlib.oneDim_isoperimetry_variance
#print axioms Arlib.isLogConcave_gaussian_shifted_real
#print axioms Arlib.oneDim_isoperimetry_gaussianFactor
#print axioms Arlib.oneDim_isoperimetry_gaussian_concaveProfile
#print axioms Arlib.concaveOn_one_sub_sq
#print axioms Arlib.one_sub_sq_not_affine
#print axioms Arlib.oneDim_isoperimetry_concaveProfile_witness
#print axioms Arlib.oneDim_isoperimetry_gaussian_concaveProfile_witness
#print axioms Arlib.oneDim_isoperimetry_gaussianFactor_unconditional
