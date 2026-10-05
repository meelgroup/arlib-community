/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Analysis.Normed.Module.HahnBanach
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Localization

/-!
# The Localization Lemma of Lovász–Simonovits: what is proved, and what is missing

The **Localization Lemma** (Lovász–Simonovits 1993 §2; Kannan–Lovász–Simonovits 1995) says:

> If `g, h : ℝⁿ → ℝ` are (lower semicontinuous) integrable functions with `∫ g > 0` and
> `∫ h > 0`, then there are points `a, b ∈ ℝⁿ` and reals `p, q ≥ 0` such that, writing
> `ℓ(t) = (1-t)p + tq`,
>
>   `∫₀¹ ℓ(t)^{n-1} g(a + t(b-a)) dt > 0`  and  `∫₀¹ ℓ(t)^{n-1} h(a + t(b-a)) dt > 0`.

That is: a two-constraint integral inequality on `ℝⁿ` can always be violated on a
one-dimensional **needle** — a segment carrying the density `ℓ^{n-1}`.

**This file does not prove that lemma in dimension `n ≥ 2`, and does not assume it either.**
Deliberately absent is any `def`/`structure`/`class`/`Prop` whose name asserts it; the only
things named below are (i) explicit functions and sets (`needleWeight`, `needleIntegral`,
`halfSpace`) and (ii) theorems proved outright.  Nothing here is a hypothesis-bundle standing in
for the conclusion.  See `CV-ROADMAP.md` §2a and the module docstring of
`Arlib.Convexity.Isoperimetry` for why that matters.

## What *is* proved here, unconditionally

**The one-dimensional case, outright** (`Arlib.localization_dim_one`).  For `n = 1` the needle
weight is `ℓ⁰ = 1`, and the lemma is a truncation statement: `∫_{-N}^{N} g → ∫_ℝ g`, so some
finite segment already carries positive mass for both `g` and `h`.  This is the base case of the
localisation induction and it is a genuine (non-vacuous) instance of the general statement.

**The needle infrastructure** (§ *needle weight*, § *needle functional*).

* `Arlib.logConcaveOn_of_concaveOn` — a nonnegative concave function is log-concave (weighted
  AM–GM).  Not in Mathlib `v4.32`.
* `Arlib.logConcaveOn_needleWeight` — the needle weight `t ↦ ((1-t)p + tq)^k` is log-concave on
  `[0,1]` for `p, q ≥ 0`.
* `Arlib.logConcaveOn_needleDensity` — hence the whole needle density
  `t ↦ ℓ(t)^k · f(a + t·v)` is log-concave on `[0,1]` whenever `f` is log-concave.  This is
  precisely the hypothesis that every one-dimensional lemma downstream (KLS95 Theorem 5.1, the
  one-dimensional isoperimetric inequality) consumes.
* `Arlib.needleIntegral` — the functional `∫₀¹ ℓ(t)^k f(a + t·v) dt` the lemma asserts to be
  positive, with `Arlib.needleIntegral_nonneg` and the closed form
  `Arlib.needleIntegral_real_exponent_zero`.

**The bisection step of the localisation induction, outright.**

* `Arlib.measure_hyperplane_eq_zero` — a hyperplane `{L = s}` is null for any additive Haar
  measure (`L ≠ 0`).
* `Arlib.continuous_setIntegral_halfSpace` — consequently `s ↦ ∫_{K ∩ {L ≤ s}} f` is
  **continuous** (dominated convergence along `𝓝 s`).
* `Arlib.exists_halfSpace_bisecting` — hence, by the intermediate value theorem, for bounded
  measurable `K`, integrable *signed* `f` and any nonzero direction `L`, some hyperplane
  orthogonal to `L` splits `∫_K f` into two exactly equal halves.
* `Arlib.exists_halfSpace_cut_pos` — **the bisection step**: if `∫_K g > 0` and `∫_K h > 0`, one
  of the two sides of a `g`-bisecting hyperplane carries `g`-mass exactly `(∫_K g)/2 > 0` *and*
  positive `h`-mass (the two `h`-masses sum to `∫_K h > 0`, so one of them is positive).  The cut
  is convex whenever `K` is.
* `Arlib.exists_bisection_chain` / `Arlib.exists_iterated_halfSpace_cut` — the step iterated: for
  every depth `N` there is a chain `K = C₀ ⊇ ⋯ ⊇ C_N`, each `C_{k+1}` literally a halfspace cut
  of `C_k` along a prescribed direction, with `∫_{C_k} g = 2^{-k} ∫_K g` (so the `g`-mass tends
  to `0`) and `∫_{C_k} h > 0` throughout.

So: **the combinatorial skeleton of the localisation argument is complete**, to any finite depth,
over a general finite-dimensional real normed space with an additive Haar measure.

## What is missing, precisely

Two independent gaps remain between `Arlib.exists_bisection_chain` and the Localization Lemma.

**(G1) Geometric decay of the nested bodies.**  Nothing above forces the `C k` to become thin:
the `g`-bisecting hyperplane in a *prescribed* direction is unique-ish, but the side that keeps
positive `h`-mass may be the fat one, so no diameter or width estimate follows.  The classical
fix is to have the freedom to keep *either* side, which needs a hyperplane bisecting `∫ g` **and**
`∫ h` simultaneously.  For two measures in `ℝⁿ` with `n ≥ 2` such a hyperplane exists, but the
proof is the Borsuk–Ulam theorem (the two-measure ham-sandwich), which **Mathlib `v4.32` does not
have** — searching its sources for `Borsuk` turns up only a bibliographic mention of the unrelated
Borsuk–Mazurkiewicz example.  Concretely the missing statement is:

  for finite signed measures `ν₁, ν₂` on `ℝⁿ` (`n ≥ 2`) absolutely continuous w.r.t. Lebesgue,
  there are `L ≠ 0` and `s` with `ν₁{L ≤ s} = ν₁{L > s}` and `ν₂{L ≤ s} = ν₂{L > s}`.

With that in hand, `Arlib.exists_halfSpace_cut_pos` would deliver *both* sides as admissible
successors.

> **⚠ CORRECTION.** This paragraph used to continue: "and a standard argument (always cut the
> current body's longest axis in half) makes the diameters decay geometrically." **That is
> false**, and it is now refuted by proof —
> `Arlib.le_diam_of_sign_separated` (`Arlib/Convexity/NeedleLimit.lean`).
>
> The recursion maintains exactly one invariant, `0 < ∫_C g` and `0 < ∫_C h`, and **that
> invariant alone bounds `diam C` from below**: positivity of `∫_C g` forces `C` to meet
> `{L ≤ a}`, positivity of `∫_C h` forces it to meet `{b ≤ L}`, so `C` spans the slab and
> `(b − a)/‖L‖ ≤ diam C`. The lemma is universally quantified over sets — no convexity, no
> dimension, no hypothesis on how `C` arose — so it kills **every** cutting scheme at once,
> adaptive or longest-axis. Granting (G1) does not help: a two-measure cut only widens the
> choice of successor, and the bound holds for both sides.
> `Arlib.one_le_diam_bisection_chain` exhibits it concretely on an explicit planar
> configuration: every body of the chain has `diam ≥ 1` at every depth, for every direction
> sequence, while its `g`-mass has already fallen to `2^{-k}/2`.
>
> The obstruction is the localization lemma's own conclusion showing through: a needle is a
> *segment*, and data whose positive parts are separated by a slab must produce a needle
> crossing that slab. **The correct target is transverse thinness** — thin in the `n−1`
> directions orthogonal to a spanning chord, with length preserved — **not small diameter.**
> Extracting that needs a bisection lemma with *positional* control over where the cut lands;
> the existential API here never reveals that.

**(G2) The limit passage, and the identification of `ℓ^{n-1}`.**  Even granted (G1), extracting
the needle requires taking a Hausdorff limit of the nested convex bodies and identifying the
limiting normalised cross-section profile as `ℓ(t)^{n-1}` with `ℓ` affine.  This needs

* the **Blaschke selection theorem** (compactness of the convex bodies of `ℝⁿ` in the Hausdorff
  metric).  Mathlib `v4.32`'s `Mathlib/Analysis/Convex/Body.lean` equips `ConvexBody V` with the
  Hausdorff metric but proves **no** compactness or selection theorem for it;
* the `1/(n-1)`-concavity of the cross-section function of a convex body — i.e. Brunn–Minkowski
  in its *sharp* `1/n`-concave form, not the log-concave form.  What this repository has is the
  log-concave form (`Arlib.isLogConcaveENN_section_volume`, Brunn's theorem), which is strictly
  weaker and does **not** determine the limit profile as a power of an affine function;
* a convergence theorem `lim (1/vol C_k) ∫_{C_k} g = ∫₀¹ ℓ^{n-1} g(a + t(b-a)) dt` for lower
  semicontinuous integrable `g`, which is where lower semicontinuity (rather than mere
  measurability) of `g` and `h` is actually used.

Neither (G1) nor (G2) reduces to lemma-sized steps from the current foundation: (G1) is a
substantial algebraic-topology development, (G2) a substantial convex-geometry one.  Estimated
honestly, each is a multi-week formalisation on its own.

## Consequence for the isoperimetric inequality

The isoperimetric inequality for log-concave densities (Cousins–Vempala §3, `thm:iso`) is a
*consumer* of the Localization Lemma together with the one-dimensional isoperimetric inequality
of Kannan–Lovász–Simonovits.  Since the Localization Lemma is not available, **that theorem is
not stated in this file, in Lean or as a predicate**, and no theorem below takes it as a
hypothesis.  What the file contributes towards it is the needle-density log-concavity that its
one-dimensional half needs, and the bisection machinery its `n`-dimensional half needs.

## References

* Lovász and Simonovits, *Random walks in a convex body and an improved volume algorithm*,
  Random Structures & Algorithms 4 (1993), §2.
* Kannan, Lovász and Simonovits, *Isoperimetric problems for convex bodies and a localization
  lemma*, Discrete & Computational Geometry 13 (1995).
* Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian Volume*,
  §3.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Arlib

/-! ### Nonnegative concave functions are log-concave -/

section ConcaveLogConcave

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **A nonnegative concave function is log-concave.**

Immediate from the two-term weighted AM–GM inequality
`Real.geom_mean_le_arith_mean2_weighted`: `f x ^ a * f y ^ b ≤ a * f x + b * f y ≤ f (a•x + b•y)`.
This is the constructor that makes the *needle weight* `ℓ ^ (n-1)` of the Localization Lemma
log-concave, `ℓ` being affine and nonnegative on the needle. -/
theorem logConcaveOn_of_concaveOn {s : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ s f)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) : LogConcaveOn s f := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  calc f x ^ a * f y ^ b ≤ a * f x + b * f y :=
        Real.geom_mean_le_arith_mean2_weighted ha hb (hf₀ hx) (hf₀ hy) hab
    _ ≤ f (a • x + b • y) := by
        have := hf.2 hx hy ha hb hab
        simpa only [smul_eq_mul] using this

end ConcaveLogConcave

/-! ### The needle weight `t ↦ ((1-t)·p + t·q) ^ k` -/

section NeedleWeight

/-- An affine function of one real variable is concave (indeed affine). -/
theorem concaveOn_affine_real {s : Set ℝ} (hs : Convex ℝ s) (c d : ℝ) :
    ConcaveOn ℝ s (fun t => c + d * t) := by
  refine ⟨hs, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h : a * (c + d * x) + b * (c + d * y) = (a + b) * c + d * (a * x + b * y) := by ring
  rw [h, hab, one_mul]

/-- **The one-dimensional weight carried by a needle**: `t ↦ ((1-t)·p + t·q) ^ k`.

In the Localization Lemma the exponent is `k = n - 1` in dimension `n`, and `p, q ≥ 0` are the
values at the two endpoints of the affine function `ℓ`. This is a plain definition of an
explicit function; it asserts nothing. -/
noncomputable def needleWeight (p q : ℝ) (k : ℕ) : ℝ → ℝ := fun t => ((1 - t) * p + t * q) ^ k

@[simp] theorem needleWeight_apply (p q : ℝ) (k : ℕ) (t : ℝ) :
    needleWeight p q k t = ((1 - t) * p + t * q) ^ k := rfl

@[simp] theorem needleWeight_zero_exponent (p q : ℝ) (t : ℝ) : needleWeight p q 0 t = 1 := by
  simp [needleWeight]

/-- The affine interpolant `t ↦ (1-t)·p + t·q` is nonnegative on `[0,1]` when `p, q ≥ 0`. -/
theorem affine_interp_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0 ≤ (1 - t) * p + t * q :=
  add_nonneg (mul_nonneg (by linarith [ht.2]) hp) (mul_nonneg ht.1 hq)

/-- The needle weight is nonnegative on `[0,1]`. -/
theorem needleWeight_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ needleWeight p q k t :=
  pow_nonneg (affine_interp_nonneg hp hq ht) k

/-- The affine interpolant is concave on `[0,1]`. -/
theorem concaveOn_affine_interp (p q : ℝ) :
    ConcaveOn ℝ (Icc (0:ℝ) 1) (fun t => (1 - t) * p + t * q) := by
  have h : (fun t : ℝ => (1 - t) * p + t * q) = fun t : ℝ => p + (q - p) * t := by
    funext t; ring
  rw [h]
  exact concaveOn_affine_real (convex_Icc 0 1) p (q - p)

/-- The affine interpolant is log-concave on `[0,1]` when `p, q ≥ 0`. -/
theorem logConcaveOn_affine_interp {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    LogConcaveOn (Icc (0:ℝ) 1) (fun t => (1 - t) * p + t * q) :=
  logConcaveOn_of_concaveOn (concaveOn_affine_interp p q) fun _ ht => affine_interp_nonneg hp hq ht

/-- **The needle weight `ℓ ^ k` is log-concave on `[0,1]`.**

The `k = n - 1` case is the weight appearing in the Localization Lemma; together with
`Arlib.logConcaveOn_needleDensity` it says that the one-dimensional measure a needle carries has
a log-concave density, which is the hypothesis every one-dimensional lemma downstream needs. -/
theorem logConcaveOn_needleWeight {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) :
    LogConcaveOn (Icc (0:ℝ) 1) (needleWeight p q k) := by
  have hrpow := (logConcaveOn_affine_interp hp hq).rpow
    (fun _ ht => affine_interp_nonneg hp hq ht) (c := (k : ℝ)) (Nat.cast_nonneg k)
  have h : (fun t : ℝ => ((1 - t) * p + t * q) ^ (k : ℝ)) = needleWeight p q k := by
    funext t
    rw [needleWeight_apply, Real.rpow_natCast]
  rwa [h] at hrpow

end NeedleWeight

/-! ### The density a needle carries -/

section NeedleDensity

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The density of a needle is log-concave.**

For a log-concave nonnegative `f : E → ℝ`, weights `p, q ≥ 0` and an exponent `k`, the
one-dimensional function

  `t ↦ ((1-t)·p + t·q)^k · f (a + t • v)`

is log-concave on `[0,1]`.  This is the object the Localization Lemma produces, and the input to
every one-dimensional argument that consumes it: the product of the needle weight
(`Arlib.logConcaveOn_needleWeight`) with the restriction of `f` to a line
(`Arlib.IsLogConcave.comp_needleMap`). -/
theorem logConcaveOn_needleDensity {f : E → ℝ} (hf : IsLogConcave f) (hf₀ : ∀ x, 0 ≤ f x)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) (a v : E) :
    LogConcaveOn (Icc (0:ℝ) 1) (fun t => needleWeight p q k t * f (needleMap a v t)) :=
  LogConcaveOn.mul (logConcaveOn_needleWeight hp hq k)
    ((hf.comp_needleMap a v).logConcaveOn (convex_Icc 0 1))
    (fun _ ht => needleWeight_nonneg hp hq k ht) (fun _ _ => hf₀ _)

/-- The needle density is nonnegative on `[0,1]`. -/
theorem needleDensity_nonneg {f : E → ℝ} (hf₀ : ∀ x, 0 ≤ f x) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (k : ℕ) (a v : E) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0 ≤ needleWeight p q k t * f (needleMap a v t) :=
  mul_nonneg (needleWeight_nonneg hp hq k ht) (hf₀ _)

end NeedleDensity

/-! ### The needle functional -/

section NeedleIntegral

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The needle functional** `∫₀¹ ((1-t)p + tq)^k · f (a + t • v) dt`.

This is the quantity the Localization Lemma asserts to be positive: in dimension `n` the exponent
is `k = n - 1` and the needle is the segment from `a` to `a + v`.  It is a plain definition of an
integral — it asserts nothing about anything. -/
noncomputable def needleIntegral (k : ℕ) (p q : ℝ) (a v : E) (f : E → ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, needleWeight p q k t * f (needleMap a v t)

/-- With exponent `0` — the one-dimensional case `n = 1` of the Localization Lemma — the needle
functional is the plain average of `f` along the segment. -/
theorem needleIntegral_exponent_zero (p q : ℝ) (a v : E) (f : E → ℝ) :
    needleIntegral 0 p q a v f = ∫ t in (0:ℝ)..1, f (needleMap a v t) := by
  simp [needleIntegral]

/-- The needle functional is monotone in the integrand, on nonnegative weights. -/
theorem needleIntegral_nonneg {f : E → ℝ} (hf₀ : ∀ x, 0 ≤ f x) {p q : ℝ} (hp : 0 ≤ p)
    (hq : 0 ≤ q) (k : ℕ) (a v : E) : 0 ≤ needleIntegral k p q a v f := by
  rw [needleIntegral, intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
  exact needleDensity_nonneg hf₀ hp hq k a v ⟨ht.1.le, ht.2⟩

end NeedleIntegral

/-! ### The Localization Lemma in dimension one -/

section DimOne

/-- The needle functional on `ℝ` with exponent `0`, in closed form: it is the mean value of `f`
over the segment `[a, b]`. -/
theorem needleIntegral_real_exponent_zero {a b : ℝ} (hab : a ≠ b) (p q : ℝ) (f : ℝ → ℝ) :
    needleIntegral 0 p q a (b - a) f = (b - a)⁻¹ * ∫ x in a..b, f x := by
  rw [needleIntegral_exponent_zero]
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hfun : (fun t : ℝ => f (needleMap a (b - a) t)) = fun t : ℝ => f (a + (b - a) * t) := by
    funext t
    rw [needleMap_apply, smul_eq_mul, mul_comm]
  rw [show (∫ t in (0:ℝ)..1, f (needleMap a (b - a) t))
      = ∫ t in (0:ℝ)..1, f (a + (b - a) * t) by rw [hfun]]
  rw [intervalIntegral.integral_comp_add_mul f hne a]
  norm_num

/-- Every real number lies in `Ioc (-n) n` for some natural `n`. -/
theorem iUnion_Ioc_neg_nat : (⋃ n : ℕ, Ioc (-(n : ℝ)) (n : ℝ)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact Set.mem_iUnion.mpr ⟨n, ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩⟩

theorem monotone_Ioc_neg_nat : Monotone fun n : ℕ => Ioc (-(n : ℝ)) (n : ℝ) := by
  intro m n hmn
  have h : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  exact Set.Ioc_subset_Ioc (by linarith) h

/-- **The Localization Lemma in dimension one.**

If `g, h : ℝ → ℝ` are integrable with `∫ g > 0` and `∫ h > 0`, then there is a needle — a
segment `[a,b]` carrying the weight `ℓ^{n-1} = ℓ^0 = 1` appropriate to dimension `n = 1` — on
which both integrals are still positive.

This is the `n = 1` instance of Lovász–Simonovits localisation, proved outright.  It is also the
base case of the localisation induction: a truncation argument, since `∫_{-N}^{N} g → ∫_ℝ g`.
The content of the lemma in dimension `n ≥ 2` is entirely in reducing to this case; see the
module docstring for what is missing there. -/
theorem localization_dim_one {g h : ℝ → ℝ} (hg : Integrable g) (hh : Integrable h)
    (hgpos : 0 < ∫ x, g x) (hhpos : 0 < ∫ x, h x) :
    ∃ a b p q : ℝ, a < b ∧ 0 ≤ p ∧ 0 ≤ q ∧
      0 < needleIntegral 0 p q a (b - a) g ∧ 0 < needleIntegral 0 p q a (b - a) h := by
  have hsm : ∀ n : ℕ, MeasurableSet (Ioc (-(n : ℝ)) (n : ℝ)) := fun _ => measurableSet_Ioc
  have key : ∀ f : ℝ → ℝ, Integrable f → 0 < (∫ x, f x) →
      ∀ᶠ n : ℕ in atTop, 0 < ∫ x in Ioc (-(n : ℝ)) (n : ℝ), f x := by
    intro f hf hfpos
    have ht := tendsto_setIntegral_of_monotone (f := f) hsm monotone_Ioc_neg_nat
      (by rw [iUnion_Ioc_neg_nat]; exact hf.integrableOn)
    rw [iUnion_Ioc_neg_nat, setIntegral_univ] at ht
    exact ht.eventually_const_lt hfpos
  obtain ⟨n, ⟨⟨hgn, hhn⟩, hn1⟩⟩ :=
    (((key g hg hgpos).and (key h hh hhpos)).and (eventually_ge_atTop 1)).exists
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  refine ⟨-(n : ℝ), (n : ℝ), 0, 0, by linarith, le_refl 0, le_refl 0, ?_, ?_⟩
  · rw [needleIntegral_real_exponent_zero (by linarith) 0 0 g,
      intervalIntegral.integral_of_le (by linarith)]
    have hpos : (0 : ℝ) < ((n : ℝ) - -(n : ℝ))⁻¹ := by
      rw [inv_pos]; linarith
    exact mul_pos hpos hgn
  · rw [needleIntegral_real_exponent_zero (by linarith) 0 0 h,
      intervalIntegral.integral_of_le (by linarith)]
    have hpos : (0 : ℝ) < ((n : ℝ) - -(n : ℝ))⁻¹ := by
      rw [inv_pos]; linarith
    exact mul_pos hpos hhn

end DimOne

/-! ### Halfspaces -/

section HalfSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The two closed/open halfspaces cut out by a linear functional.**

`halfSpace L s true = {x | L x ≤ s}` and `halfSpace L s false = {x | s < L x}`.  Taking one
closed and one open makes the pair an exact partition of the space, which is what the bisection
step needs.  This is a plain definition of an explicit set. -/
def halfSpace (L : E →L[ℝ] ℝ) (s : ℝ) (side : Bool) : Set E :=
  if side then {x | L x ≤ s} else {x | s < L x}

@[simp] theorem halfSpace_true (L : E →L[ℝ] ℝ) (s : ℝ) :
    halfSpace L s true = {x | L x ≤ s} := rfl

@[simp] theorem halfSpace_false (L : E →L[ℝ] ℝ) (s : ℝ) :
    halfSpace L s false = {x | s < L x} := rfl

theorem isLinear_clm (L : E →L[ℝ] ℝ) : IsLinearMap ℝ (L : E → ℝ) :=
  ⟨fun x y => L.map_add x y, fun c x => L.map_smul c x⟩

/-- The closed side `{L ≤ s}` of a cut is closed. -/
theorem isClosed_halfSpace_true (L : E →L[ℝ] ℝ) (s : ℝ) : IsClosed (halfSpace L s true) := by
  rw [halfSpace_true]
  exact isClosed_le L.continuous continuous_const

@[simp] theorem closure_halfSpace_true (L : E →L[ℝ] ℝ) (s : ℝ) :
    closure (halfSpace L s true) = halfSpace L s true :=
  (isClosed_halfSpace_true L s).closure_eq

/-- **The closure of the *open* side of a cut is again a closed side of a cut** — namely the
closed side of the *opposite* functional, `{x | s ≤ L x} = halfSpace (-L) (-s) true`.

This is what lets a construction that cuts with `Arlib.halfSpace` — whose `false` side is open, so
that the two sides partition the space exactly — be closed up after the fact without leaving the
class of sets the construction talks about: every closure of a cut body is again contained in a
*closed* half-space of the same family, with `L` replaced by `-L` and `s` by `-s`.  For the pencil
of `Arlib.Convexity.LocalizationAssembly` the sign flip is a half-turn of the angle
(`Arlib.pencilFun_add_pi`), so the family of cuts is literally preserved. -/
theorem closure_halfSpace_false_subset (L : E →L[ℝ] ℝ) (s : ℝ) :
    closure (halfSpace L s false) ⊆ halfSpace (-L) (-s) true := by
  refine closure_minimal (fun x hx => ?_) (isClosed_halfSpace_true (-L) (-s))
  rw [halfSpace_false, mem_setOf_eq] at hx
  simp only [halfSpace_true, mem_setOf_eq, ContinuousLinearMap.neg_apply]
  linarith

/-- **Closing up a cut, uniformly in the side.**  The closure of either side of the cut
`(L, s)` is contained in the closed half-space `{L' ≤ s'}` for `(L', s')` equal to `(L, s)` or to
`(-L, -s)`.  The `true` side is already closed; the `false` side is handled by
`Arlib.closure_halfSpace_false_subset`. -/
theorem exists_closure_halfSpace_subset (L : E →L[ℝ] ℝ) (s : ℝ) (side : Bool) :
    ∃ (L' : E →L[ℝ] ℝ) (s' : ℝ), ((L' = L ∧ s' = s) ∨ (L' = -L ∧ s' = -s)) ∧
      closure (halfSpace L s side) ⊆ halfSpace L' s' true := by
  cases side
  · exact ⟨-L, -s, Or.inr ⟨rfl, rfl⟩, closure_halfSpace_false_subset L s⟩
  · exact ⟨L, s, Or.inl ⟨rfl, rfl⟩, (closure_halfSpace_true L s).subset⟩

/-- Both halfspaces are convex. -/
theorem convex_halfSpace (L : E →L[ℝ] ℝ) (s : ℝ) (side : Bool) :
    Convex ℝ (halfSpace L s side) := by
  cases side
  · exact convex_halfSpace_gt (isLinear_clm L) s
  · exact convex_halfSpace_le (isLinear_clm L) s

/-- The two halfspaces are complementary. -/
theorem halfSpace_false_eq_compl (L : E →L[ℝ] ℝ) (s : ℝ) :
    halfSpace L s false = (halfSpace L s true)ᶜ := by
  ext x; simp [not_le]

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- Both halfspaces are measurable. -/
theorem measurableSet_halfSpace (L : E →L[ℝ] ℝ) (s : ℝ) (side : Bool) :
    MeasurableSet (halfSpace L s side) := by
  cases side
  · exact measurableSet_lt measurable_const L.continuous.measurable
  · exact measurableSet_le L.continuous.measurable measurable_const

end HalfSpace

/-! ### A hyperplane is null -/

section Hyperplane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **A hyperplane `{x | L x = s}` is null for every additive Haar measure**, for `L ≠ 0`.

It is a translate of `ker L`, a strict submodule, so `Measure.addHaar_submodule` applies.  This
is what makes the cut mass `s ↦ ∫_{K ∩ {L ≤ s}} g` *continuous*, which is the intermediate-value
input of the bisection step. -/
theorem measure_hyperplane_eq_zero {L : E →L[ℝ] ℝ} (hL : L ≠ 0) (s : ℝ) :
    μ {x : E | L x = s} = 0 := by
  rcases Set.eq_empty_or_nonempty {x : E | L x = s} with hemp | ⟨x₀, hx₀⟩
  · rw [hemp, measure_empty]
  · have hx₀' : L x₀ = s := hx₀
    have hker : LinearMap.ker (L : E →ₗ[ℝ] ℝ) ≠ ⊤ := by
      intro htop
      refine hL (ContinuousLinearMap.ext fun x => ?_)
      have hx : x ∈ LinearMap.ker (L : E →ₗ[ℝ] ℝ) := by rw [htop]; exact Submodule.mem_top
      simpa using hx
    have hpre : (fun y : E => x₀ + y) ⁻¹' {x : E | L x = s}
        = ((LinearMap.ker (L : E →ₗ[ℝ] ℝ) : Submodule ℝ E) : Set E) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, map_add, SetLike.mem_coe,
        LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [hx₀']
      constructor
      · intro h; linarith
      · intro h; rw [h]; ring
    rw [← measure_preimage_add μ x₀ _, hpre]
    exact Measure.addHaar_submodule μ _ hker

end Hyperplane

/-! ### The bisection step of the localisation induction -/

section Bisection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- `‖1_S f x‖ ≤ |f x|` pointwise. -/
theorem norm_indicator_le_abs {α : Type*} (S : Set α) (f : α → ℝ) (x : α) :
    ‖Set.indicator S f x‖ ≤ |f x| := by
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact abs_nonneg _

/-- **The mass on one side of a moving hyperplane is a continuous function of its position.**

`s ↦ ∫_{K ∩ {L ≤ s}} f` is continuous.  This is dominated convergence along the filter `𝓝 s`,
the a.e. pointwise convergence of the indicators being exactly the statement that the hyperplane
`{L = s}` is null (`Arlib.measure_hyperplane_eq_zero`). -/
theorem continuous_setIntegral_halfSpace {f : E → ℝ} {K : Set E} (hf : IntegrableOn f K μ)
    {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    Continuous fun s : ℝ => ∫ x in K ∩ {x : E | L x ≤ s}, f x ∂μ := by
  have hmeasL : ∀ s : ℝ, MeasurableSet {x : E | L x ≤ s} := fun s =>
    measurableSet_le L.continuous.measurable measurable_const
  have hrepr : ∀ s : ℝ, ∫ x in K ∩ {x : E | L x ≤ s}, f x ∂μ
      = ∫ x in K, Set.indicator {x : E | L x ≤ s} f x ∂μ := fun s =>
    (setIntegral_indicator (hmeasL s)).symm
  simp_rw [hrepr]
  rw [continuous_iff_continuousAt]
  intro s
  have hnull : (μ.restrict K) {x : E | L x = s} = 0 := by
    have h1 : (μ.restrict K) {x : E | L x = s} ≤ μ {x : E | L x = s} :=
      Measure.le_iff'.mp Measure.restrict_le_self _
    rw [measure_hyperplane_eq_zero μ hL s] at h1
    exact nonpos_iff_eq_zero.mp h1
  have hae : ∀ᵐ x ∂(μ.restrict K), L x ≠ s := by
    rw [ae_iff]
    simpa using hnull
  refine tendsto_integral_filter_of_dominated_convergence (fun x => |f x|)
    (Eventually.of_forall fun t => hf.aestronglyMeasurable.indicator (hmeasL t))
    (Eventually.of_forall fun t => Eventually.of_forall fun x => norm_indicator_le_abs _ _ x)
    hf.abs ?_
  filter_upwards [hae] with x hx
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hmem : x ∈ {y : E | L y ≤ s} := le_of_lt hlt
    rw [Set.indicator_of_mem hmem]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioi_mem_nhds hlt] with t ht
    have hxt : x ∈ {y : E | L y ≤ t} := le_of_lt (Set.mem_Ioi.mp ht)
    exact (Set.indicator_of_mem hxt f).symm
  · have hnmem : x ∉ {y : E | L y ≤ s} := not_le.mpr hgt
    rw [Set.indicator_of_notMem hnmem]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Iio_mem_nhds hgt] with t ht
    have hxt : x ∉ {y : E | L y ≤ t} := not_le.mpr (Set.mem_Iio.mp ht)
    exact (Set.indicator_of_notMem hxt f).symm

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- **The two halfspace cuts of `K` split every integral over `K`.** -/
theorem setIntegral_halfSpace_add {f : E → ℝ} {K : Set E} (hf : IntegrableOn f K μ)
    (hK : MeasurableSet K) (L : E →L[ℝ] ℝ) (s : ℝ) :
    ∫ x in K ∩ halfSpace L s true, f x ∂μ + ∫ x in K ∩ halfSpace L s false, f x ∂μ
      = ∫ x in K, f x ∂μ := by
  have hA : MeasurableSet (halfSpace L s true) := measurableSet_halfSpace L s true
  have hB : MeasurableSet (halfSpace L s false) := measurableSet_halfSpace L s false
  have hdisj : Disjoint (K ∩ halfSpace L s true) (K ∩ halfSpace L s false) := by
    rw [halfSpace_false_eq_compl]
    exact Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right
      disjoint_compl_right
  have hunion : (K ∩ halfSpace L s true) ∪ (K ∩ halfSpace L s false) = K := by
    rw [halfSpace_false_eq_compl, ← Set.inter_union_distrib_left, Set.union_compl_self,
      Set.inter_univ]
  calc ∫ x in K ∩ halfSpace L s true, f x ∂μ + ∫ x in K ∩ halfSpace L s false, f x ∂μ
      = ∫ x in (K ∩ halfSpace L s true) ∪ (K ∩ halfSpace L s false), f x ∂μ :=
        (setIntegral_union hdisj (hK.inter hB) (hf.mono_set Set.inter_subset_left)
          (hf.mono_set Set.inter_subset_left)).symm
    _ = ∫ x in K, f x ∂μ := by rw [hunion]

/-- **Existence of a mass-bisecting hyperplane in a prescribed direction.**

For a bounded measurable `K`, an integrable `f` and any nonzero direction `L`, some translate of
the hyperplane `{L = s}` splits `∫_K f` into two exactly equal halves.  The proof is the
intermediate value theorem applied to `Arlib.continuous_setIntegral_halfSpace`: for `s` below
`K` the cut mass is `0`, for `s` above `K` it is `∫_K f`.

No sign hypothesis on `f` is needed — `f` is signed in the localisation argument. -/
theorem exists_halfSpace_bisecting {f : E → ℝ} {K : Set E} (hf : IntegrableOn f K μ)
    (hKb : Bornology.IsBounded K) {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∃ s : ℝ, ∫ x in K ∩ halfSpace L s true, f x ∂μ = (∫ x in K, f x ∂μ) / 2 := by
  set F : ℝ → ℝ := fun s => ∫ x in K ∩ {x : E | L x ≤ s}, f x ∂μ with hF
  have hFc : Continuous F := continuous_setIntegral_halfSpace hf hL
  obtain ⟨r, hr⟩ := hKb.subset_closedBall (0 : E)
  have hLb : ∀ x ∈ K, |L x| ≤ ‖L‖ * r := by
    intro x hx
    have hx' : ‖x‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hr hx
    calc |L x| = ‖L x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * r := mul_le_mul_of_nonneg_left hx' (norm_nonneg L)
  -- below `K` the cut is empty
  have hlow : F (-(‖L‖ * r) - 1) = 0 := by
    have hempty : K ∩ {x : E | L x ≤ -(‖L‖ * r) - 1} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      have h1 : -(‖L‖ * r) ≤ L x := neg_le_of_abs_le (hLb x hx.1)
      have h2 : L x ≤ -(‖L‖ * r) - 1 := hx.2
      linarith
    rw [hF]
    simp only
    rw [hempty, setIntegral_empty]
  -- above `K` the cut is everything
  have hhigh : F (‖L‖ * r) = ∫ x in K, f x ∂μ := by
    have hall : K ∩ {x : E | L x ≤ ‖L‖ * r} = K := by
      refine Set.inter_eq_self_of_subset_left fun x hx => ?_
      exact le_of_abs_le (hLb x hx)
    rw [hF]
    simp only
    rw [hall]
  set c : ℝ := (∫ x in K, f x ∂μ) / 2 with hc
  have hobtain : ∃ s : ℝ, F s = c := by
    rcases le_total 0 (∫ x in K, f x ∂μ) with hpos | hneg
    · refine intermediate_value_univ₂ (a := -(‖L‖ * r) - 1) (b := ‖L‖ * r) hFc
        continuous_const ?_ ?_
      · rw [hlow]; positivity
      · rw [hhigh, hc]; linarith
    · refine intermediate_value_univ₂ (a := ‖L‖ * r) (b := -(‖L‖ * r) - 1) hFc
        continuous_const ?_ ?_
      · rw [hhigh, hc]; linarith
      · rw [hlow, hc]; linarith
  obtain ⟨s, hs⟩ := hobtain
  exact ⟨s, hs⟩

/-- **The bisection step of the Localization Lemma.**

Given a bounded measurable `K` on which both `∫ g` and `∫ h` are positive, and any nonzero
direction `L`, there is a halfspace cut of `K` — one of the two sides of a hyperplane orthogonal
to `L` — on which **both** integrals are still positive, and on which the `g`-mass is *exactly
halved*.

This is the inductive step of the Lovász–Simonovits localisation argument, proved outright: the
`g`-bisecting hyperplane exists by `Arlib.exists_halfSpace_bisecting`, both of its sides then
carry `g`-mass exactly `(∫_K g)/2 > 0`, and since the two `h`-masses sum to `∫_K h > 0` at least
one side also carries positive `h`-mass.

The cut is convex whenever `K` is, so the induction stays inside the class of convex bodies. -/
theorem exists_halfSpace_cut_pos {g h : E → ℝ} {K : Set E} (hg : IntegrableOn g K μ)
    (hh : IntegrableOn h K μ) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    {L : E →L[ℝ] ℝ} (hL : L ≠ 0) (hgK : 0 < ∫ x in K, g x ∂μ) (hhK : 0 < ∫ x in K, h x ∂μ) :
    ∃ (s : ℝ) (side : Bool),
      MeasurableSet (K ∩ halfSpace L s side) ∧
      K ∩ halfSpace L s side ⊆ K ∧
      (Convex ℝ K → Convex ℝ (K ∩ halfSpace L s side)) ∧
      ∫ x in K ∩ halfSpace L s side, g x ∂μ = (∫ x in K, g x ∂μ) / 2 ∧
      0 < ∫ x in K ∩ halfSpace L s side, g x ∂μ ∧
      0 < ∫ x in K ∩ halfSpace L s side, h x ∂μ := by
  obtain ⟨s, hs⟩ := exists_halfSpace_bisecting hg hKb hL
  have hgsum := setIntegral_halfSpace_add hg hK L s
  have hgfalse : ∫ x in K ∩ halfSpace L s false, g x ∂μ = (∫ x in K, g x ∂μ) / 2 := by
    linarith [hgsum, hs]
  have hhsum := setIntegral_halfSpace_add hh hK L s
  have hside : 0 < ∫ x in K ∩ halfSpace L s true, h x ∂μ ∨
      0 < ∫ x in K ∩ halfSpace L s false, h x ∂μ := by
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    linarith [hcon.1, hcon.2, hhsum, hhK]
  have hbasic : ∀ side : Bool,
      MeasurableSet (K ∩ halfSpace L s side) ∧ K ∩ halfSpace L s side ⊆ K ∧
        (Convex ℝ K → Convex ℝ (K ∩ halfSpace L s side)) := by
    intro side
    exact ⟨hK.inter (measurableSet_halfSpace L s side), Set.inter_subset_left,
      fun hconv => hconv.inter (convex_halfSpace L s side)⟩
  rcases hside with hpos | hpos
  · exact ⟨s, true, (hbasic true).1, (hbasic true).2.1, (hbasic true).2.2, hs,
      by rw [hs]; exact half_pos hgK, hpos⟩
  · exact ⟨s, false, (hbasic false).1, (hbasic false).2.1, (hbasic false).2.2, hgfalse,
      by rw [hgfalse]; exact half_pos hgK, hpos⟩

/-- **The bisection step iterates.**

For every `N` there is a subset `C ⊆ K`, obtained from `K` by `N` successive halfspace cuts
(the `k`-th orthogonal to `L k`), which is still measurable, bounded, and convex if `K` was, on
which the `g`-mass is *exactly* `2^{-N}` of the original — so it tends to `0` — while the
`h`-mass is *still positive*.

This is the localisation induction, run to any finite depth.  What it does **not** provide is
geometric control: nothing here forces the sets `C` to become thin, and that is precisely the
missing ingredient discussed in the module docstring. -/
theorem exists_iterated_halfSpace_cut {g h : E → ℝ} (hg : Integrable g μ) (hh : Integrable h μ)
    (L : ℕ → (E →L[ℝ] ℝ)) (hL : ∀ k, L k ≠ 0) {K : Set E} (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (hgK : 0 < ∫ x in K, g x ∂μ) (hhK : 0 < ∫ x in K, h x ∂μ) :
    ∀ N : ℕ, ∃ C : Set E, C ⊆ K ∧ MeasurableSet C ∧ Bornology.IsBounded C ∧
      (Convex ℝ K → Convex ℝ C) ∧
      ∫ x in C, g x ∂μ = (∫ x in K, g x ∂μ) / 2 ^ N ∧ 0 < ∫ x in C, h x ∂μ := by
  intro N
  induction N with
  | zero => exact ⟨K, Set.Subset.rfl, hK, hKb, fun hc => hc, by simp, hhK⟩
  | succ N ih =>
    obtain ⟨C, hCK, hCm, hCb, hCc, hCg, hCh⟩ := ih
    have hgC : 0 < ∫ x in C, g x ∂μ := by
      rw [hCg]
      exact div_pos hgK (by positivity)
    obtain ⟨s, side, hDm, hDsub, hDc, hDg, _, hDh⟩ :=
      exists_halfSpace_cut_pos (hg.integrableOn) (hh.integrableOn) hCm hCb (hL N) hgC hCh
    refine ⟨C ∩ halfSpace (L N) s side, hDsub.trans hCK, hDm, hCb.subset hDsub,
      fun hconv => hDc (hCc hconv), ?_, hDh⟩
    rw [hDg, hCg, pow_succ]
    ring

/-- **The localisation induction, as a chain of halfspace cuts.**

For every depth `N` there is a chain `K = C₀ ⊇ C₁ ⊇ ⋯ ⊇ C_N` in which each `C (k+1)` is *literally*
one of the two sides of a hyperplane orthogonal to `L k` intersected with `C k`, every `C k` is
measurable, bounded and convex whenever `K` is, the `g`-mass of `C k` is **exactly** `2^{-k}` of
the `g`-mass of `K`, and the `h`-mass of every `C k` is **still positive**.

This is `Arlib.exists_halfSpace_cut_pos` iterated, and it is the complete combinatorial skeleton
of the Lovász–Simonovits localisation argument: it produces, to any finite depth, the nested
bodies on which both constraints survive.  What it does **not** produce is any *geometric* decay:
nothing here forces the `C k` to become thin, so no limiting needle can be extracted from it.
See the module docstring for exactly what would be needed. -/
theorem exists_bisection_chain {g h : E → ℝ} (hg : Integrable g μ) (hh : Integrable h μ)
    (L : ℕ → (E →L[ℝ] ℝ)) (hL : ∀ k, L k ≠ 0) {K : Set E} (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (hgK : 0 < ∫ x in K, g x ∂μ) (hhK : 0 < ∫ x in K, h x ∂μ) :
    ∀ N : ℕ, ∃ C : ℕ → Set E, C 0 = K ∧
      (∀ k, k < N → ∃ (s : ℝ) (side : Bool), C (k + 1) = C k ∩ halfSpace (L k) s side) ∧
      (∀ k, k ≤ N → MeasurableSet (C k) ∧ Bornology.IsBounded (C k) ∧
        (Convex ℝ K → Convex ℝ (C k)) ∧
        ∫ x in C k, g x ∂μ = (∫ x in K, g x ∂μ) / 2 ^ k ∧ 0 < ∫ x in C k, h x ∂μ) := by
  intro N
  induction N with
  | zero =>
    refine ⟨fun _ => K, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => ?_⟩
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    exact ⟨hK, hKb, fun hc => hc, by simp, hhK⟩
  | succ N ih =>
    obtain ⟨C, hC0, hCstep, hCinv⟩ := ih
    obtain ⟨hNm, hNb, hNc, hNg, hNh⟩ := hCinv N le_rfl
    have hgN : 0 < ∫ x in C N, g x ∂μ := by
      rw [hNg]; exact div_pos hgK (by positivity)
    obtain ⟨s, side, hDm, hDsub, hDc, hDg, _, hDh⟩ :=
      exists_halfSpace_cut_pos hg.integrableOn hh.integrableOn hNm hNb (hL N) hgN hNh
    obtain ⟨C', hC'⟩ : ∃ C' : ℕ → Set E, ∀ k,
        C' k = if k = N + 1 then C N ∩ halfSpace (L N) s side else C k := ⟨_, fun _ => rfl⟩
    have hlow : ∀ k, k ≠ N + 1 → C' k = C k := fun k hk => by rw [hC' k, if_neg hk]
    have htop : C' (N + 1) = C N ∩ halfSpace (L N) s side := by rw [hC' (N + 1), if_pos rfl]
    refine ⟨C', ?_, ?_, ?_⟩
    · rw [hlow 0 (by omega)]
      exact hC0
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkN | hkN
      · obtain ⟨s', side', hstep⟩ := hCstep k hkN
        refine ⟨s', side', ?_⟩
        rw [hlow (k + 1) (by omega), hlow k (by omega)]
        exact hstep
      · refine ⟨s, side, ?_⟩
        rw [hkN, htop, hlow N (by omega)]
    · intro k hk
      rcases Nat.eq_or_lt_of_le hk with hkeq | hklt
      · rw [hkeq, htop]
        refine ⟨hDm, hNb.subset hDsub, fun hc => hDc (hNc hc), ?_, hDh⟩
        rw [hDg, hNg, pow_succ]
        ring
      · rw [hlow k (by omega)]
        exact hCinv k (by omega)

/-- **Non-vacuity of the bisection step, with content.**

Every hypothesis of `Arlib.exists_halfSpace_cut_pos` is met by the unit ball with `g = h = 1`,
and a nonzero direction exists as soon as `E` is nontrivial.  So the bisection step is not a
statement about an empty configuration: it genuinely produces a halfspace that cuts the volume of
a ball exactly in two.  (A hypothesis-bundle that only degenerate data satisfies proves nothing;
this is the check that rules that out here.) -/
theorem exists_halfSpace_cut_pos_unitBall [Nontrivial E] :
    ∃ (L : E →L[ℝ] ℝ) (s : ℝ) (side : Bool), L ≠ 0 ∧
      (0 : ℝ) < ∫ _x in Metric.closedBall (0 : E) 1 ∩ halfSpace L s side, (1 : ℝ) ∂μ ∧
      ∫ _x in Metric.closedBall (0 : E) 1 ∩ halfSpace L s side, (1 : ℝ) ∂μ
        = (∫ _x in Metric.closedBall (0 : E) 1, (1 : ℝ) ∂μ) / 2 := by
  obtain ⟨y, hy⟩ := exists_norm_ne_zero E
  obtain ⟨L, hLnorm, -⟩ := exists_dual_vector ℝ y hy
  have hL : L ≠ 0 := by
    intro h
    rw [h, norm_zero] at hLnorm
    exact zero_ne_one hLnorm
  have hKm : MeasurableSet (Metric.closedBall (0 : E) 1) := measurableSet_closedBall
  have hKb : Bornology.IsBounded (Metric.closedBall (0 : E) 1) := Metric.isBounded_closedBall
  have hKfin : μ (Metric.closedBall (0 : E) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hKpos : 0 < μ (Metric.closedBall (0 : E) 1) := Metric.measure_closedBall_pos μ 0 one_pos
  have hint : IntegrableOn (fun _ : E => (1 : ℝ)) (Metric.closedBall (0 : E) 1) μ :=
    integrableOn_const hKfin
  have hIpos : (0 : ℝ) < ∫ _x in Metric.closedBall (0 : E) 1, (1 : ℝ) ∂μ := by
    rw [setIntegral_const, smul_eq_mul, mul_one]
    exact ENNReal.toReal_pos hKpos.ne' hKfin
  obtain ⟨s, side, -, -, -, heq, hpos, -⟩ :=
    exists_halfSpace_cut_pos hint hint hKm hKb hL hIpos hIpos
  exact ⟨L, s, side, hL, hpos, heq⟩

end Bisection

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`.  In
particular nothing below depends on `sorryAx` or on any locally declared axiom — there are none
in this file. -/

#print axioms logConcaveOn_of_concaveOn
#print axioms concaveOn_affine_real
#print axioms affine_interp_nonneg
#print axioms needleWeight_nonneg
#print axioms concaveOn_affine_interp
#print axioms logConcaveOn_affine_interp
#print axioms logConcaveOn_needleWeight
#print axioms logConcaveOn_needleDensity
#print axioms needleDensity_nonneg
#print axioms needleIntegral_exponent_zero
#print axioms needleIntegral_nonneg
#print axioms needleIntegral_real_exponent_zero
#print axioms iUnion_Ioc_neg_nat
#print axioms monotone_Ioc_neg_nat
#print axioms localization_dim_one
#print axioms convex_halfSpace
#print axioms measurableSet_halfSpace
#print axioms isClosed_halfSpace_true
#print axioms closure_halfSpace_true
#print axioms closure_halfSpace_false_subset
#print axioms exists_closure_halfSpace_subset
#print axioms halfSpace_false_eq_compl
#print axioms measure_hyperplane_eq_zero
#print axioms norm_indicator_le_abs
#print axioms continuous_setIntegral_halfSpace
#print axioms setIntegral_halfSpace_add
#print axioms exists_halfSpace_bisecting
#print axioms exists_halfSpace_cut_pos
#print axioms exists_iterated_halfSpace_cut
#print axioms exists_bisection_chain
#print axioms exists_halfSpace_cut_pos_unitBall

end Arlib
