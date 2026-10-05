/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationTransverse

/-!
# The localisation needle from a chain whose slab *shrinks* to the needle

`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` asks every body of the chain to lie in
**and** span one fixed slab `{y | φ (y - a) ∈ [0,1]}`.  Together those two hypotheses force
`φ '' (D k - a) = [0,1]` at every stage — the needle has to realise the full height of `D 0` —
which no genuinely shrinking localisation chain can do: a chain shrinks in *every* direction, so
its height range shrinks too.  That is item **(E)** of `Arlib.Convexity.LocalizationAssembly`.

This file removes the rigidity.  The `k`-th body is asked to lie in and span its **own** slab
`{y | φ (y - a) ∈ [l k, u k]}`, with

* `Icc 0 1 ⊆ Icc (l k) (u k)` — the limit slab sits inside every stage's slab, and
* `l k → 0`, `u k → 1` — the stages' slabs shrink down to the limit slab.

Both are automatic for a decreasing chain of compact convex bodies once the *limit* segment is
normalised to unit height: `l k` and `u k` are then simply the minimum and maximum of the height
functional on `D k`, they are monotone by nesting, and their limits are the endpoints of the
limit segment.  Nothing is assumed about how fast the slabs shrink.

## The mechanism

Rescaling the height of the `k`-th body by the affine map `s ↦ l k + s (u k - l k)` carries its
slab onto `[0,1]`, and — because that map touches only the height coordinate — carries slices to
slices.  The **rescaled** normalised slice profiles `Arlib.rescaledProfile` therefore all live on
`[0,1]`, are nonnegative with concave `1/m`-th powers there, integrate to `1`, and are bounded by
`2 ^ (m + 1)` uniformly; so the Arzelà–Ascoli selection of `Arlib.Convexity.ConcaveSelection`
applies to *them* verbatim.  The only new analytic input is that the needle *point* moves with
`k`: the height `s` of the rescaled body sits at height `l k + s (u k - l k)` of the original
one, and the integrand has to be evaluated there.  Continuity of the integrand plus `l k → 0`,
`u k → 1` closes that gap inside the same dominated-convergence step.

No metric decay, no Hausdorff convergence and no rate is used or claimed.

## Main results

* `Arlib.integral_comp_affine_line` — the one-dimensional change of variables `t = l + s c`.
* `Arlib.le_two_pow_of_concaveOn_rpow` — **the profile bound, in one dimension**: a nonnegative
  function on `ℝ`, vanishing off `[0,1]`, with a concave `1/m`-th power there and integral `1`,
  is bounded by `2 ^ (m + 1)`.  This is `Arlib.normalised_volume_slice_le` with the geometry
  stripped out, which is what lets it be applied to a *rescaled* profile.
* `Arlib.rescaledProfile` — the plain formula `(u - l) · vol (slice C (l + s (u - l))) / vol C`.
* `Arlib.rescaledProfile_nonneg`, `Arlib.rescaledProfile_eq_zero_of_notMem`,
  `Arlib.integral_rescaledProfile`, `Arlib.concaveOn_rescaledProfile_rpow`,
  `Arlib.rescaledProfile_le` — its five properties.
* `Arlib.exists_subseq_tendsto_rescaledProfile` — the selection: a subsequence along which the
  rescaled profiles converge pointwise to a `W ≥ 0` with `W ^ (1/m)` concave on `(0,1)`.
* `Arlib.tendsto_average_setIntegral_of_rescaledProfile` — the limit passage with a moving slab.
* `Arlib.exists_needleIntegral_eq_zero_and_pos_shrinkingSlab` — **the needle theorem, in frame**,
  with the fixed slab replaced by a shrinking one.

## Honesty note

This file contains **no** `structure`, `class` or named `Prop`, and no theorem below takes the
Localization Lemma, the isoperimetric inequality or Dyer–Frieze as a hypothesis.  The single
`def` (`Arlib.rescaledProfile`) is an explicit formula, and every property attributed to it is
proved.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Arlib

/-! ### One-dimensional groundwork -/

section OneDim

/-- **The one-dimensional change of variables `t = b + s c`,** for `c > 0`.  Stated for the
integral over all of `ℝ`, where it needs no integrability hypothesis: both sides are `0` when the
integrand is not integrable. -/
theorem integral_comp_affine_line (g : ℝ → ℝ) (b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, g (b + s * c) = c⁻¹ * ∫ t : ℝ, g t := by
  have h1 : (∫ s : ℝ, g (b + s * c)) = ∫ s : ℝ, (fun y : ℝ => g (b + y)) (s * c) := rfl
  rw [h1, Measure.integral_comp_mul_right (fun y : ℝ => g (b + y)) c,
    integral_add_left_eq_self g b, smul_eq_mul, abs_of_pos (inv_pos.mpr hc)]

/-- **The profile bound, in one dimension.**

A nonnegative `F : ℝ → ℝ` which vanishes off `[0,1]`, whose `1/m`-th power is concave on `[0,1]`,
and whose integral is `1`, is bounded by `2 ^ (m + 1)` everywhere.

This is `Arlib.normalised_volume_slice_le` with all the geometry removed: the profile enters only
through the three displayed properties.  That is exactly what makes it applicable to the
*rescaled* profile of a body sitting in a slab other than `[0,1]`.

No measurability hypothesis is needed: a non-integrable function has integral `0 ≠ 1`, so `F` is
integrable automatically. -/
theorem le_two_pow_of_concaveOn_rpow {m : ℕ} (hm : m ≠ 0) {F : ℝ → ℝ} (hF0 : ∀ t, 0 ≤ F t)
    (hFconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => F t ^ (1 / (m : ℝ))))
    (hFoff : ∀ t, t ∉ Icc (0 : ℝ) 1 → F t = 0) (hFint : ∫ t : ℝ, F t = 1) (t : ℝ) :
    F t ≤ 2 ^ (m + 1) := by
  have hFI : Integrable F := by
    by_contra hcon
    rw [integral_undef hcon] at hFint
    exact zero_ne_one hFint
  have hu0 : ∀ r : ℝ, (0 : ℝ) ≤ F r ^ (1 / (m : ℝ)) := fun r => Real.rpow_nonneg (hF0 r) _
  have hum : ∀ r : ℝ, (F r ^ (1 / (m : ℝ))) ^ m = F r := by
    intro r; rw [one_div]; exact Real.rpow_inv_natCast_pow (hF0 r) hm
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  swap
  · rw [hFoff t ht]; positivity
  have hlowF : ∀ r ∈ Icc (t / 2) ((1 + t) / 2), ((F t ^ (1 / (m : ℝ))) / 2) ^ m ≤ F r := by
    intro r hr
    rw [← hum r]
    have hhalf := half_le_of_concaveOn_Icc hFconc (fun x _ => hu0 x) ht hr.1 hr.2
    have h0 : (0 : ℝ) ≤ (F t ^ (1 / (m : ℝ))) / 2 := by
      have := hu0 t; linarith
    gcongr
  have hJvol : (volume (Icc (t / 2) ((1 + t) / 2))).toReal = 1 / 2 := by
    rw [Real.volume_Icc, show (1 + t) / 2 - t / 2 = 1 / 2 by ring]
    norm_num
  have hJtop : volume (Icc (t / 2) ((1 + t) / 2)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hkey : ((F t ^ (1 / (m : ℝ))) / 2) ^ m * (1 / 2) ≤ 1 := by
    calc ((F t ^ (1 / (m : ℝ))) / 2) ^ m * (1 / 2)
        = ((F t ^ (1 / (m : ℝ))) / 2) ^ m * (volume (Icc (t / 2) ((1 + t) / 2))).toReal := by
          rw [hJvol]
      _ ≤ ∫ r in Icc (t / 2) ((1 + t) / 2), F r := by
          have h := setIntegral_ge_of_const_le_real (μ := (volume : Measure ℝ))
            (s := Icc (t / 2) ((1 + t) / 2)) measurableSet_Icc hJtop hlowF hFI.integrableOn
          simpa [Measure.real] using h
      _ ≤ ∫ r : ℝ, F r := setIntegral_le_integral hFI (Eventually.of_forall hF0)
      _ = 1 := hFint
  have hrw : ((F t ^ (1 / (m : ℝ))) / 2) ^ m * (1 / 2)
      = (F t ^ (1 / (m : ℝ))) ^ m / 2 ^ (m + 1) := by
    rw [div_pow, pow_succ]; ring
  rw [hrw, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (m + 1)), hum t, one_mul] at hkey
  exact hkey

/-- Concavity is preserved by the affine reparametrisation `s ↦ l + s (u - l)` of `[0,1]` onto
`[l, u]`. -/
theorem concaveOn_comp_lineMap {h : ℝ → ℝ} {l u : ℝ} (hlu : l < u)
    (hh : ConcaveOn ℝ (Icc l u) h) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun s => h (l + s * (u - l))) := by
  have hd : (0 : ℝ) < u - l := by linarith
  have hmem : ∀ x ∈ Icc (0 : ℝ) 1, l + x * (u - l) ∈ Icc l u := by
    rintro x ⟨hx0, hx1⟩
    exact ⟨by nlinarith, by nlinarith⟩
  refine ⟨convex_Icc 0 1, fun x hx y hy p q hp hq hpq => ?_⟩
  have hkey : l + (p • x + q • y) * (u - l)
      = p • (l + x * (u - l)) + q • (l + y * (u - l)) := by
    simp only [smul_eq_mul]; linear_combination (-l) * hpq
  show p • h (l + x * (u - l)) + q • h (l + y * (u - l)) ≤ h (l + (p • x + q • y) * (u - l))
  rw [hkey]
  exact hh.2 (hmem x hx) (hmem y hy) hp hq hpq

end OneDim

/-! ### The rescaled slice profile -/

section RescaledProfile

variable {m : ℕ}

/-- **The normalised slice profile of `C`, rescaled from the slab `[l, u]` onto `[0,1]`.**

A plain explicit formula: the point at height `s ∈ [0,1]` of the rescaled body is the point at
height `l + s (u - l)` of `C`, and the factor `u - l` is the Jacobian that keeps the total
integral equal to `1`.  Since the reparametrisation touches only the height coordinate, the
slices themselves are untouched, which is what makes the five lemmas below cheap. -/
noncomputable def rescaledProfile (C : Set (Fin (m + 1) → ℝ)) (l u : ℝ) (s : ℝ) : ℝ :=
  (u - l) * ((volume (slice C (l + s * (u - l)))).toReal / (volume C).toReal)

theorem rescaledProfile_nonneg {C : Set (Fin (m + 1) → ℝ)} {l u : ℝ} (hlu : l < u) (s : ℝ) :
    0 ≤ rescaledProfile C l u s :=
  mul_nonneg (by linarith) (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

theorem measurable_rescaledProfile {C : Set (Fin (m + 1) → ℝ)} (hCm : MeasurableSet C)
    (l u : ℝ) : Measurable (rescaledProfile C l u) := by
  have h1 : Measurable fun s : ℝ => l + s * (u - l) :=
    measurable_const.add (measurable_id.mul_const _)
  exact ((measurable_volume_slice_toReal hCm).comp h1).div_const _ |>.const_mul _

/-- Off `[0,1]` the rescaled profile vanishes, because the corresponding height lies outside the
slab in which `C` sits. -/
theorem rescaledProfile_eq_zero_of_notMem {C : Set (Fin (m + 1) → ℝ)} {l u : ℝ} (hlu : l < u)
    (hslab : ∀ x ∈ C, x 0 ∈ Icc l u) {s : ℝ} (hs : s ∉ Icc (0 : ℝ) 1) :
    rescaledProfile C l u s = 0 := by
  have hd : (0 : ℝ) < u - l := by linarith
  have hout : l + s * (u - l) ∉ Icc l u := by
    rintro ⟨h1, h2⟩
    exact hs ⟨by nlinarith, by nlinarith⟩
  have hempty : slice C (l + s * (u - l)) = ∅ :=
    Set.eq_empty_of_forall_notMem fun y hy => hout (by simpa using hslab _ hy)
  rw [rescaledProfile, hempty, measure_empty]
  simp

/-- **The rescaled profile is a probability density on `[0,1]`.**  The Jacobian `u - l` is exactly
what makes the total mass `1`; `Arlib.integral_volume_slice` supplies the unrescaled statement. -/
theorem integral_rescaledProfile {C : Set (Fin (m + 1) → ℝ)} (hCm : MeasurableSet C)
    (hCfin : volume C ≠ ⊤) (hCpos : 0 < volume C) {l u : ℝ} (hlu : l < u) :
    ∫ s : ℝ, rescaledProfile C l u s = 1 := by
  have hd : (0 : ℝ) < u - l := by linarith
  have hVpos : (0 : ℝ) < (volume C).toReal := ENNReal.toReal_pos hCpos.ne' hCfin
  have hbase : (∫ s : ℝ, (volume (slice C (l + s * (u - l)))).toReal)
      = (u - l)⁻¹ * ∫ t : ℝ, (volume (slice C t)).toReal :=
    integral_comp_affine_line (fun t => (volume (slice C t)).toReal) l hd
  calc ∫ s : ℝ, rescaledProfile C l u s
      = (u - l) * ((∫ s : ℝ, (volume (slice C (l + s * (u - l)))).toReal)
          / (volume C).toReal) := by
        simp only [rescaledProfile]
        rw [integral_const_mul, integral_div]
    _ = (u - l) * (((u - l)⁻¹ * (volume C).toReal) / (volume C).toReal) := by
        rw [hbase, integral_volume_slice hCm hCfin]
    _ = 1 := by field_simp

/-- **The `1/m`-th power of the rescaled profile is concave on `[0,1]`.**  Sharp Brunn
(`Arlib.brunn_slice_concaveOn`) on the slab `[l, u]`, transported by the affine
reparametrisation. -/
theorem concaveOn_rescaledProfile_rpow (hm : m ≠ 0) {C : Set (Fin (m + 1) → ℝ)}
    (hconv : Convex ℝ C) (hCm : MeasurableSet C) {l u : ℝ} (hlu : l < u)
    (hspan : ∀ t ∈ Icc l u, (slice C t).Nonempty) (hsfin : ∀ t : ℝ, volume (slice C t) ≠ ⊤) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun s => rescaledProfile C l u s ^ (1 / (m : ℝ))) := by
  have hd : (0 : ℝ) < u - l := by linarith
  have hc0 : (0 : ℝ) ≤ ((u - l) / (volume C).toReal) ^ (1 / (m : ℝ)) :=
    Real.rpow_nonneg (div_nonneg hd.le ENNReal.toReal_nonneg) _
  have hbase : ConcaveOn ℝ (Icc l u) (fun t => (volume (slice C t)).toReal ^ (1 / (m : ℝ))) :=
    brunn_slice_concaveOn hm hconv hCm (convex_Icc l u) hspan (fun t _ => hsfin t)
  have hcomp := concaveOn_comp_lineMap hlu hbase
  have heq : (fun s => rescaledProfile C l u s ^ (1 / (m : ℝ)))
      = fun s => ((u - l) / (volume C).toReal) ^ (1 / (m : ℝ))
          • ((volume (slice C (l + s * (u - l)))).toReal ^ (1 / (m : ℝ))) := by
    funext s
    rw [smul_eq_mul, ← Real.mul_rpow (div_nonneg hd.le ENNReal.toReal_nonneg)
      ENNReal.toReal_nonneg]
    congr 1
    rw [rescaledProfile]
    ring
  rw [heq]
  exact hcomp.smul hc0

/-- **The rescaled profiles are bounded by `2 ^ (m + 1)`, uniformly over all slabs.**

`Arlib.le_two_pow_of_concaveOn_rpow` applied to the rescaled profile — this is (G2b) for a body
whose slab is *not* the unit slab, and the point of doing the bound in one dimension is exactly
that the constant does not degrade as the slab moves. -/
theorem rescaledProfile_le (hm : m ≠ 0) {C : Set (Fin (m + 1) → ℝ)} (hconv : Convex ℝ C)
    (hCm : MeasurableSet C) (hCfin : volume C ≠ ⊤) (hCpos : 0 < volume C)
    (hsfin : ∀ t : ℝ, volume (slice C t) ≠ ⊤) {l u : ℝ} (hlu : l < u)
    (hslab : ∀ x ∈ C, x 0 ∈ Icc l u) (hspan : ∀ t ∈ Icc l u, (slice C t).Nonempty) (s : ℝ) :
    rescaledProfile C l u s ≤ 2 ^ (m + 1) :=
  le_two_pow_of_concaveOn_rpow hm (rescaledProfile_nonneg hlu)
    (concaveOn_rescaledProfile_rpow hm hconv hCm hlu hspan hsfin)
    (fun _ hr => rescaledProfile_eq_zero_of_notMem hlu hslab hr)
    (integral_rescaledProfile hCm hCfin hCpos hlu) s

/-- **The selection, for a sequence of bodies in *moving* slabs.**

`Arlib.exists_subseq_tendsto_of_concaveOn_Ioo` applied to the `1/m`-th powers of the *rescaled*
profiles.  Because rescaling puts every body's profile on the same interval `[0,1]`, the
Arzelà–Ascoli argument of `Arlib.Convexity.ConcaveSelection` applies verbatim, with the uniform
bound `2 ^ (m + 1)` supplied by `Arlib.rescaledProfile_le`.

The limit `W` is delivered nonnegative with a **concave** `1/m`-th power on `(0,1)`, i.e.
`W = ℓ^m` for a concave `ℓ` — the concave form of the Localization Lemma. -/
theorem exists_subseq_tendsto_rescaledProfile (hm : m ≠ 0)
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hconv : ∀ k, Convex ℝ (C k))
    (hCm : ∀ k, MeasurableSet (C k)) (hCfin : ∀ k, volume (C k) ≠ ⊤)
    (hCpos : ∀ k, 0 < volume (C k)) (hsfin : ∀ k, ∀ t : ℝ, volume (slice (C k) t) ≠ ⊤)
    {l u : ℕ → ℝ} (hlu : ∀ k, l k < u k)
    (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (l k) (u k))
    (hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), (slice (C k) t).Nonempty) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∀ s : ℝ, Tendsto (fun k => rescaledProfile (C (ψ k)) (l (ψ k)) (u (ψ k)) s) atTop
        (𝓝 (W s))) ∧
      ∀ s : ℝ, W s ≤ 2 ^ (m + 1) := by
  have hminv : (0 : ℝ) < 1 / (m : ℝ) := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    positivity
  have hp0 : ∀ (k : ℕ) (s : ℝ), 0 ≤ rescaledProfile (C k) (l k) (u k) s :=
    fun k s => rescaledProfile_nonneg (hlu k) s
  have hpB : ∀ (k : ℕ) (s : ℝ), rescaledProfile (C k) (l k) (u k) s ≤ 2 ^ (m + 1) :=
    fun k s => rescaledProfile_le hm (hconv k) (hCm k) (hCfin k) (hCpos k) (hsfin k) (hlu k)
      (hslab k) (hspan k) s
  have hpoff : ∀ (k : ℕ) (s : ℝ), s ∉ Icc (0 : ℝ) 1 →
      rescaledProfile (C k) (l k) (u k) s = 0 :=
    fun k s hs => rescaledProfile_eq_zero_of_notMem (hlu k) (hslab k) hs
  have hconc : ∀ k : ℕ, ConcaveOn ℝ (Ioo (0 : ℝ) 1)
      (fun s => rescaledProfile (C k) (l k) (u k) s ^ (1 / (m : ℝ))) :=
    fun k => (concaveOn_rescaledProfile_rpow hm (hconv k) (hCm k) (hlu k) (hspan k)
      (hsfin k)).subset Ioo_subset_Icc_self (convex_Ioo 0 1)
  obtain ⟨ψ, hψ, V, hV⟩ := exists_subseq_tendsto_of_concaveOn_Ioo hconc
    (fun k s => Real.rpow_nonneg (hp0 k s) _)
    (M := (2 ^ (m + 1) : ℝ) ^ (1 / (m : ℝ)))
    (fun k s => Real.rpow_le_rpow (hp0 k s) (hpB k s) hminv.le)
    (fun k s hs => by rw [hpoff k s hs, Real.zero_rpow hminv.ne'])
  have hV0 : ∀ s : ℝ, 0 ≤ V s := fun s =>
    ge_of_tendsto' (hV s) (fun k => Real.rpow_nonneg (hp0 _ s) _)
  have hpow : ∀ (k : ℕ) (s : ℝ),
      (rescaledProfile (C k) (l k) (u k) s ^ (1 / (m : ℝ))) ^ m
        = rescaledProfile (C k) (l k) (u k) s := by
    intro k s; rw [one_div]; exact Real.rpow_inv_natCast_pow (hp0 k s) hm
  have hlim : ∀ s : ℝ,
      Tendsto (fun k => rescaledProfile (C (ψ k)) (l (ψ k)) (u (ψ k)) s) atTop (𝓝 (V s ^ m)) := by
    intro s
    simpa only [hpow] using (hV s).pow m
  refine ⟨ψ, hψ, fun s => V s ^ m, fun s => pow_nonneg (hV0 s) m, ?_, hlim, ?_⟩
  · have heq : (fun t => (V t ^ m) ^ (1 / (m : ℝ))) = V := by
      funext t; rw [one_div]; exact Real.pow_rpow_inv_natCast (hV0 t) hm
    rw [heq]
    exact concaveOn_of_tendsto (convex_Ioo (0 : ℝ) 1) (fun i => hconc (ψ i)) (fun x _ => hV x)
  · exact fun s => le_of_tendsto (hlim s) (Eventually.of_forall fun k => hpB _ s)

end RescaledProfile

/-! ### The limit passage with a moving slab -/

section MovingSlab

variable {m : ℕ}

/-- The parametrisation `t ↦ (t, 0, …, 0)` of the first coordinate axis is continuous. -/
theorem continuous_consAxis (m : ℕ) :
    Continuous fun t : ℝ => (Fin.cons t (0 : Fin m → ℝ) : Fin (m + 1) → ℝ) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simpa only [Fin.cons_zero] using continuous_id'
  · intro j; simpa only [Fin.cons_succ] using continuous_const

/-- **The needle integral of a body, read off its rescaled profile.**

Substituting `t = l + s (u - l)` in `∫ vol(slice C t)/vol C · f(axis t) dt`.  The Jacobian is
absorbed by the factor `u - l` built into `Arlib.rescaledProfile`. -/
theorem integral_slice_profile_eq_integral_rescaledProfile {C : Set (Fin (m + 1) → ℝ)}
    {l u : ℝ} (hlu : l < u) (f : (Fin (m + 1) → ℝ) → ℝ) :
    (∫ t : ℝ, ((volume (slice C t)).toReal / (volume C).toReal)
        * f (Fin.cons t (0 : Fin m → ℝ)))
      = ∫ s : ℝ, rescaledProfile C l u s
          * f (Fin.cons (l + s * (u - l)) (0 : Fin m → ℝ)) := by
  have hd : (0 : ℝ) < u - l := by linarith
  set G : ℝ → ℝ := fun t => ((volume (slice C t)).toReal / (volume C).toReal)
    * f (Fin.cons t (0 : Fin m → ℝ)) with hG
  have hpt : ∀ s : ℝ, rescaledProfile C l u s
      * f (Fin.cons (l + s * (u - l)) (0 : Fin m → ℝ)) = (u - l) * G (l + s * (u - l)) := by
    intro s; rw [hG, rescaledProfile]; ring
  rw [show (∫ s : ℝ, rescaledProfile C l u s
        * f (Fin.cons (l + s * (u - l)) (0 : Fin m → ℝ)))
      = ∫ s : ℝ, (u - l) * G (l + s * (u - l)) from
    integral_congr_ae (Eventually.of_forall hpt),
    integral_const_mul, integral_comp_affine_line G l hd, ← mul_assoc,
    mul_inv_cancel₀ hd.ne', one_mul]

/-- **The limit passage, with the slab moving from stage to stage.**

`Arlib.tendsto_average_setIntegral_of_profile` with the fixed unit slab replaced by the slabs
`[l k, u k]`, which are only asked to satisfy `l k → 0` and `u k → 1`.

Two things change relative to the fixed-slab statement.  The profile hypotheses are stated for
the **rescaled** profiles, all of which live on `[0,1]`; and the needle point at rescaled height
`s` is `l k + s (u k - l k)`, which moves with `k`.  Continuity of `f` turns that motion into
pointwise convergence of the integrand, and the same dominated-convergence step absorbs it.

Transverse thinness enters only through `Arlib.abs_setIntegral_sub_slice_profile_le`, exactly as
before, and is unaffected by the slab moving. -/
theorem tendsto_average_setIntegral_of_rescaledProfile
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hCm : ∀ k, MeasurableSet (C k))
    (hCfin : ∀ k, volume (C k) ≠ ⊤) (hCpos : ∀ k, 0 < volume (C k))
    {l u : ℕ → ℝ} (hlu : ∀ k, l k < u k)
    (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (l k) (u k))
    (hl : Tendsto l atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 1))
    {f : (Fin (m + 1) → ℝ) → ℝ} (hfc : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    {δ : ℕ → ℝ} (hδ : ∀ k, ∀ x ∈ C k, |f x - f (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0)) {W : ℝ → ℝ} {B : ℝ}
    (hB : ∀ k, ∀ s : ℝ, rescaledProfile (C k) (l k) (u k) s ≤ B)
    (hlim : ∀ s : ℝ, Tendsto (fun k => rescaledProfile (C k) (l k) (u k) s) atTop (𝓝 (W s))) :
    Tendsto (fun k => (∫ x in C k, f x) / (volume (C k)).toReal) atTop
      (𝓝 (∫ s : ℝ, W s * f (Fin.cons s (0 : Fin m → ℝ)))) := by
  have hfm : Measurable f := hfc.measurable
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hVpos : ∀ k, 0 < (volume (C k)).toReal := fun k =>
    ENNReal.toReal_pos (hCpos k).ne' (hCfin k)
  have hp0 : ∀ (k : ℕ) (s : ℝ), 0 ≤ rescaledProfile (C k) (l k) (u k) s :=
    fun k s => rescaledProfile_nonneg (hlu k) s
  have hpoff : ∀ (k : ℕ) (s : ℝ), s ∉ Icc (0 : ℝ) 1 →
      rescaledProfile (C k) (l k) (u k) s = 0 :=
    fun k s hs => rescaledProfile_eq_zero_of_notMem (hlu k) (hslab k) hs
  have hB0 : (0 : ℝ) ≤ B := by
    have h := hB 0 2
    rwa [hpoff 0 2 (by norm_num)] at h
  -- the moving axis point converges
  have haxis : ∀ s : ℝ, Tendsto (fun k => l k + s * (u k - l k)) atTop (𝓝 s) := by
    intro s
    have h := hl.add (((hu.sub hl).const_mul s))
    simpa using h
  have hfaxis : ∀ s : ℝ, Tendsto
      (fun k => f (Fin.cons (l k + s * (u k - l k)) (0 : Fin m → ℝ))) atTop
      (𝓝 (f (Fin.cons s (0 : Fin m → ℝ)))) := fun s =>
    ((hfc.comp (continuous_consAxis m)).continuousAt.tendsto).comp (haxis s)
  -- Step 1: the thin-tube comparison, normalised
  have hstep1 : ∀ k, |(∫ x in C k, f x) / (volume (C k)).toReal
      - ∫ s : ℝ, rescaledProfile (C k) (l k) (u k) s
          * f (Fin.cons (l k + s * (u k - l k)) (0 : Fin m → ℝ))| ≤ δ k := by
    intro k
    have hA := abs_setIntegral_sub_slice_profile_le (hCm k) (hCfin k) hfm (M := M)
      (fun x _ => hM x) (hδ k)
    rw [← integral_slice_profile_eq_integral_rescaledProfile (hlu k) f]
    have hgint : (∫ t : ℝ, ((volume (slice (C k) t)).toReal / (volume (C k)).toReal)
          * f (Fin.cons t (0 : Fin m → ℝ)))
        = (∫ t : ℝ, (volume (slice (C k) t)).toReal * f (Fin.cons t (0 : Fin m → ℝ)))
          / (volume (C k)).toReal := by
      rw [← integral_div]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring)
    rw [hgint, div_sub_div_same, abs_div, abs_of_pos (hVpos k), div_le_iff₀ (hVpos k)]
    exact hA
  -- Step 2: dominated convergence for the rescaled profile integrals
  have hmeas : ∀ k, AEStronglyMeasurable (fun s : ℝ => rescaledProfile (C k) (l k) (u k) s
      * f (Fin.cons (l k + s * (u k - l k)) (0 : Fin m → ℝ))) (volume : Measure ℝ) := by
    intro k
    have h1 : Measurable fun s : ℝ => l k + s * (u k - l k) :=
      measurable_const.add (measurable_id.mul_const _)
    exact ((measurable_rescaledProfile (hCm k) (l k) (u k)).mul
      ((hfm.comp (measurable_consAxis m)).comp h1)).aestronglyMeasurable
  have hbound : Integrable ((Icc (0 : ℝ) 1).indicator fun _ => B * M) (volume : Measure ℝ) := by
    refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hdom : ∀ k, ∀ᵐ s : ℝ, ‖rescaledProfile (C k) (l k) (u k) s
      * f (Fin.cons (l k + s * (u k - l k)) (0 : Fin m → ℝ))‖
        ≤ (Icc (0 : ℝ) 1).indicator (fun _ => B * M) s := by
    intro k
    refine Eventually.of_forall fun s => ?_
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 k s)]
      exact mul_le_mul (hB k s) (hM _) (abs_nonneg _) hB0
    · rw [Set.indicator_of_notMem hs, hpoff k s hs]
      simp
  have hptlim : ∀ᵐ s : ℝ, Tendsto (fun k => rescaledProfile (C k) (l k) (u k) s
      * f (Fin.cons (l k + s * (u k - l k)) (0 : Fin m → ℝ))) atTop
      (𝓝 (W s * f (Fin.cons s (0 : Fin m → ℝ)))) :=
    Eventually.of_forall fun s => (hlim s).mul (hfaxis s)
  have hstep2 : Tendsto (fun k => ∫ s : ℝ, rescaledProfile (C k) (l k) (u k) s
      * f (Fin.cons (l k + s * (u k - l k)) (0 : Fin m → ℝ))) atTop
      (𝓝 (∫ s : ℝ, W s * f (Fin.cons s (0 : Fin m → ℝ)))) :=
    tendsto_integral_of_dominated_convergence _ hmeas hbound hdom hptlim
  have hstep3 : Tendsto (fun k => (∫ x in C k, f x) / (volume (C k)).toReal
      - ∫ s : ℝ, rescaledProfile (C k) (l k) (u k) s
          * f (Fin.cons (l k + s * (u k - l k)) (0 : Fin m → ℝ))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => by simpa [Real.norm_eq_abs] using hstep1 k) hδ0
  have := hstep3.add hstep2
  simpa using this

/-- **The localisation needle in the frame, from a chain whose slab shrinks.**

`Arlib.exists_needleIntegral_eq_zero_and_pos` with the fixed unit slab replaced by the moving
slabs `[l k, u k]`, subject only to `l k → 0` and `u k → 1`.  The two conclusions are unchanged,
and `W` still comes out nonnegative with a **concave** `1/m`-th power on `(0,1)`, **supported in
`[0,1]`** and **integrable**.

Support and integrability are stated because every downstream consumer needs them: each rescaled
profile vanishes off `[0,1]` (`Arlib.rescaledProfile_eq_zero_of_notMem`) and is bounded by
`2^(m+1)` (`Arlib.rescaledProfile_le`), both properties pass to the pointwise limit, and the limit
is measurable by `Arlib.measurable_rescaledProfile`, so
`Arlib.integrable_of_forall_notMem_Icc` applies.

Both invariants pass to the limit for the same reasons as before: the `g₁`-averages are
*identically* `0`, so no limit theorem can degrade the equality, and the `g₂`-averages are
bounded below by `ε`, which survives as a non-strict inequality and is still positive. -/
theorem exists_needleIntegral_eq_zero_and_pos_shrinkingSlab (hm : m ≠ 0)
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hconv : ∀ k, Convex ℝ (C k))
    (hCm : ∀ k, MeasurableSet (C k)) (hCfin : ∀ k, volume (C k) ≠ ⊤)
    (hCpos : ∀ k, 0 < volume (C k)) (hsfin : ∀ k, ∀ t : ℝ, volume (slice (C k) t) ≠ ⊤)
    {l u : ℕ → ℝ} (hlu : ∀ k, l k < u k)
    (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (l k) (u k))
    (hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), (slice (C k) t).Nonempty)
    (hl : Tendsto l atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 1))
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    {δ : ℕ → ℝ}
    (hδ₁ : ∀ k, ∀ x ∈ C k, |g₁ x - g₁ (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ₂ : ∀ k, ∀ x ∈ C k, |g₂ x - g₂ (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hzero : ∀ k, (∫ x in C k, g₁ x) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (C k)).toReal ≤ ∫ x in C k, g₂ x) :
    ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (Fin.cons t (0 : Fin m → ℝ))) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (Fin.cons t (0 : Fin m → ℝ)) := by
  obtain ⟨ψ, hψ, W, hW0, hWc, hWlim, hWB⟩ := exists_subseq_tendsto_rescaledProfile hm hconv hCm
    hCfin hCpos hsfin hlu hslab hspan
  have hVpos : ∀ k, 0 < (volume (C k)).toReal := fun k =>
    ENNReal.toReal_pos (hCpos k).ne' (hCfin k)
  have hpass : ∀ {f : (Fin (m + 1) → ℝ) → ℝ}, Continuous f → (∀ x, |f x| ≤ M) →
      (∀ k, ∀ x ∈ C k, |f x - f (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k) →
      Tendsto (fun k => (∫ x in C (ψ k), f x) / (volume (C (ψ k))).toReal) atTop
        (𝓝 (∫ s : ℝ, W s * f (Fin.cons s (0 : Fin m → ℝ)))) := by
    intro f hfc hfM hfδ
    exact tendsto_average_setIntegral_of_rescaledProfile (C := fun k => C (ψ k))
      (l := fun k => l (ψ k)) (u := fun k => u (ψ k)) (fun k => hCm (ψ k)) (fun k => hCfin (ψ k))
      (fun k => hCpos (ψ k)) (fun k => hlu (ψ k)) (fun k => hslab (ψ k))
      (hl.comp hψ.tendsto_atTop) (hu.comp hψ.tendsto_atTop) hfc hfM
      (δ := fun k => δ (ψ k)) (fun k => hfδ (ψ k)) (hδ0.comp hψ.tendsto_atTop)
      (B := 2 ^ (m + 1))
      (fun k s => rescaledProfile_le hm (hconv (ψ k)) (hCm (ψ k)) (hCfin (ψ k)) (hCpos (ψ k))
        (hsfin (ψ k)) (hlu (ψ k)) (hslab (ψ k)) (hspan (ψ k)) s)
      hWlim
  -- the rescaled profiles vanish off `[0,1]`, hence so does their pointwise limit
  have hWsupp : ∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0 := by
    intro t ht
    have hconst : (fun k => rescaledProfile (C (ψ k)) (l (ψ k)) (u (ψ k)) t)
        = fun _ : ℕ => (0 : ℝ) :=
      funext fun k => rescaledProfile_eq_zero_of_notMem (hlu (ψ k)) (hslab (ψ k)) ht
    have h := hWlim t
    rw [hconst] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hWm : Measurable W := by
    refine measurable_of_tendsto_metrizable' atTop
      (f := fun k => rescaledProfile (C (ψ k)) (l (ψ k)) (u (ψ k)))
      (fun k => measurable_rescaledProfile (hCm (ψ k)) _ _) ?_
    exact tendsto_pi_nhds.mpr hWlim
  refine ⟨W, hW0, hWsupp, integrable_of_forall_notMem_Icc hWm hW0 hWB hWsupp, hWc, ?_, ?_⟩
  · refine tendsto_nhds_unique (hpass hg₁ hM₁ hδ₁) ?_
    have hconst : (fun k => (∫ x in C (ψ k), g₁ x) / (volume (C (ψ k))).toReal)
        = fun _ : ℕ => (0 : ℝ) := by
      funext k; rw [hzero (ψ k), zero_div]
    rw [hconst]
    exact tendsto_const_nhds
  · refine lt_of_lt_of_le hεpos (ge_of_tendsto (hpass hg₂ hM₂ hδ₂) ?_)
    refine Eventually.of_forall fun k => ?_
    rw [le_div_iff₀ (hVpos (ψ k))]
    exact hge (ψ k)

end MovingSlab

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.integral_comp_affine_line
#print axioms Arlib.le_two_pow_of_concaveOn_rpow
#print axioms Arlib.concaveOn_comp_lineMap
#print axioms Arlib.rescaledProfile_nonneg
#print axioms Arlib.measurable_rescaledProfile
#print axioms Arlib.rescaledProfile_eq_zero_of_notMem
#print axioms Arlib.integral_rescaledProfile
#print axioms Arlib.concaveOn_rescaledProfile_rpow
#print axioms Arlib.rescaledProfile_le
#print axioms Arlib.exists_subseq_tendsto_rescaledProfile
#print axioms Arlib.continuous_consAxis
#print axioms Arlib.integral_slice_profile_eq_integral_rescaledProfile
#print axioms Arlib.tendsto_average_setIntegral_of_rescaledProfile
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_shrinkingSlab
