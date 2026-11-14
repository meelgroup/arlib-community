/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationAffine
import ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationClosed

section
/-!
# The localisation needle from a chain whose slab *shrinks* to the needle

`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact` asks every body of the chain to lie in
**and** span one fixed slab `{y | φ (y - a) ∈ [0,1]}`.  Together those two hypotheses force
`φ '' (D k - a) = [0,1]` at every stage — the needle has to realise the full height of `D 0` —
which no genuinely shrinking localisation chain can do: a chain shrinks in *every* direction, so
its height range shrinks too.  That is item **(E)** of `ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationAssembly`.

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
slices.  The **rescaled** normalised slice profiles `ArlibCommunity.Foundations.Convex.rescaledProfile` therefore all live on
`[0,1]`, are nonnegative with concave `1/m`-th powers there, integrate to `1`, and are bounded by
`2 ^ (m + 1)` uniformly; so the Arzelà–Ascoli selection of `ArlibCommunity.Foundations.Convex.Localization.Analysis.ConcaveSelection`
applies to *them* verbatim.  The only new analytic input is that the needle *point* moves with
`k`: the height `s` of the rescaled body sits at height `l k + s (u k - l k)` of the original
one, and the integrand has to be evaluated there.  Continuity of the integrand plus `l k → 0`,
`u k → 1` closes that gap inside the same dominated-convergence step.

No metric decay, no Hausdorff convergence and no rate is used or claimed.

## Main results

* `ArlibCommunity.Foundations.Convex.integral_comp_affine_line` — the one-dimensional change of variables `t = l + s c`.
* `ArlibCommunity.Foundations.Convex.le_two_pow_of_concaveOn_rpow` — **the profile bound, in one dimension**: a nonnegative
  function on `ℝ`, vanishing off `[0,1]`, with a concave `1/m`-th power there and integral `1`,
  is bounded by `2 ^ (m + 1)`.  This is `ArlibCommunity.Foundations.Convex.normalised_volume_slice_le` with the geometry
  stripped out, which is what lets it be applied to a *rescaled* profile.
* `ArlibCommunity.Foundations.Convex.rescaledProfile` — the plain formula `(u - l) · vol (slice C (l + s (u - l))) / vol C`.
* `ArlibCommunity.Foundations.Convex.rescaledProfile_nonneg`, `ArlibCommunity.Foundations.Convex.rescaledProfile_eq_zero_of_notMem`,
  `ArlibCommunity.Foundations.Convex.integral_rescaledProfile`, `ArlibCommunity.Foundations.Convex.concaveOn_rescaledProfile_rpow`,
  `ArlibCommunity.Foundations.Convex.rescaledProfile_le` — its five properties.
* `ArlibCommunity.Foundations.Convex.exists_subseq_tendsto_rescaledProfile` — the selection: a subsequence along which the
  rescaled profiles converge pointwise to a `W ≥ 0` with `W ^ (1/m)` concave on `(0,1)`.
* `ArlibCommunity.Foundations.Convex.tendsto_average_setIntegral_of_rescaledProfile` — the limit passage with a moving slab.
* `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_shrinkingSlab` — **the needle theorem, in frame**,
  with the fixed slab replaced by a shrinking one.

## Honesty note

This file contains **no** `structure`, `class` or named `Prop`, and no theorem below takes the
Localization Lemma, the isoperimetric inequality or Dyer–Frieze as a hypothesis.  The single
`def` (`ArlibCommunity.Foundations.Convex.rescaledProfile`) is an explicit formula, and every property attributed to it is
proved.
-/

open MeasureTheory Set Filter
open scoped ENNReal _root_.Topology


open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

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

This is `ArlibCommunity.Foundations.Convex.normalised_volume_slice_le` with all the geometry removed: the profile enters only
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
what makes the total mass `1`; `ArlibCommunity.Foundations.Convex.integral_volume_slice` supplies the unrescaled statement. -/
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
(`ArlibCommunity.Foundations.Convex.brunn_slice_concaveOn`) on the slab `[l, u]`, transported by the affine
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

`ArlibCommunity.Foundations.Convex.le_two_pow_of_concaveOn_rpow` applied to the rescaled profile — this is (G2b) for a body
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

`ArlibCommunity.Foundations.Convex.exists_subseq_tendsto_of_concaveOn_Ioo` applied to the `1/m`-th powers of the *rescaled*
profiles.  Because rescaling puts every body's profile on the same interval `[0,1]`, the
Arzelà–Ascoli argument of `ArlibCommunity.Foundations.Convex.Localization.Analysis.ConcaveSelection` applies verbatim, with the uniform
bound `2 ^ (m + 1)` supplied by `ArlibCommunity.Foundations.Convex.rescaledProfile_le`.

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
absorbed by the factor `u - l` built into `ArlibCommunity.Foundations.Convex.rescaledProfile`. -/
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

`ArlibCommunity.Foundations.Convex.tendsto_average_setIntegral_of_profile` with the fixed unit slab replaced by the slabs
`[l k, u k]`, which are only asked to satisfy `l k → 0` and `u k → 1`.

Two things change relative to the fixed-slab statement.  The profile hypotheses are stated for
the **rescaled** profiles, all of which live on `[0,1]`; and the needle point at rescaled height
`s` is `l k + s (u k - l k)`, which moves with `k`.  Continuity of `f` turns that motion into
pointwise convergence of the integrand, and the same dominated-convergence step absorbs it.

Transverse thinness enters only through `ArlibCommunity.Foundations.Convex.abs_setIntegral_sub_slice_profile_le`, exactly as
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

`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos` with the fixed unit slab replaced by the moving
slabs `[l k, u k]`, subject only to `l k → 0` and `u k → 1`.  The two conclusions are unchanged,
and `W` still comes out nonnegative with a **concave** `1/m`-th power on `(0,1)`, **supported in
`[0,1]`** and **integrable**.

Support and integrability are stated because every downstream consumer needs them: each rescaled
profile vanishes off `[0,1]` (`ArlibCommunity.Foundations.Convex.rescaledProfile_eq_zero_of_notMem`) and is bounded by
`2^(m+1)` (`ArlibCommunity.Foundations.Convex.rescaledProfile_le`), both properties pass to the pointwise limit, and the limit
is measurable by `ArlibCommunity.Foundations.Convex.measurable_rescaledProfile`, so
`ArlibCommunity.Foundations.Convex.integrable_of_forall_notMem_Icc` applies.

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

end ArlibCommunity.Foundations.Convex

/-! ### Axiom audit -/

#print axioms ArlibCommunity.Foundations.Convex.integral_comp_affine_line
#print axioms ArlibCommunity.Foundations.Convex.le_two_pow_of_concaveOn_rpow
#print axioms ArlibCommunity.Foundations.Convex.concaveOn_comp_lineMap
#print axioms ArlibCommunity.Foundations.Convex.rescaledProfile_nonneg
#print axioms ArlibCommunity.Foundations.Convex.measurable_rescaledProfile
#print axioms ArlibCommunity.Foundations.Convex.rescaledProfile_eq_zero_of_notMem
#print axioms ArlibCommunity.Foundations.Convex.integral_rescaledProfile
#print axioms ArlibCommunity.Foundations.Convex.concaveOn_rescaledProfile_rpow
#print axioms ArlibCommunity.Foundations.Convex.rescaledProfile_le
#print axioms ArlibCommunity.Foundations.Convex.exists_subseq_tendsto_rescaledProfile
#print axioms ArlibCommunity.Foundations.Convex.continuous_consAxis
#print axioms ArlibCommunity.Foundations.Convex.integral_slice_profile_eq_integral_rescaledProfile
#print axioms ArlibCommunity.Foundations.Convex.tendsto_average_setIntegral_of_rescaledProfile
#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_shrinkingSlab

end

section
/-!
# The localisation needle in general position, from a chain whose slab shrinks

`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_shrinkingSlab`
(`ArlibCommunity.Foundations.Convex.Localization.Analysis.NeedleSlab`) is stated in the frame in which the needle is the first coordinate
axis.  This file carries it to general position and hands it the geometry that
`ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact` actually produces, closing item **(E)** of
`ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationAssembly`.

The rigidity that item (E) records is that
`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact` asks all bodies to lie in *and* span one
fixed slab, which forces the height range to be constant along the chain.  Here the `k`-th body
lies in and spans its **own** slab `[l k, u k]`, with `l k ≤ 0`, `1 ≤ u k`, `l k → 0`, `u k → 1`:
the slabs *shrink*, from outside, onto the slab of the limit needle.  For a decreasing chain of
compact convex bodies `l k` and `u k` are simply the minimum and maximum of the height functional
on `D k`, so both hypotheses are automatic once the limit segment has been normalised to unit
height.

## Main results

* `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_affine_shrinkingSlab` — (G2c) for a shrinking
  slab: an arbitrary needle `t ↦ a + t • v` and an arbitrary height functional `φ` with `φ v = 1`.
* `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact_shrinkingSlab` — the transverse-thinness
  hypothesis discharged from compactness, via `ArlibCommunity.Foundations.Convex.exists_tendsto_transverse_modulus_pair`.
* `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab` — the `haxis`
  hypothesis replaced by `Collinear ℝ (⋂ k, D k)`, which is exactly what the localisation chain
  delivers.
* `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_shrinking_box` — **the acid test**: the genuinely
  shrinking boxes `D k = [-1/(k+1), 1 + 1/(k+1)] × [-1/(k+1), 1/(k+1)]^m`, which shrink in
  *every* direction including along the needle, satisfy every hypothesis at once.  The fixed-slab
  form cannot accept them: their height range is `[-1/(k+1), 1 + 1/(k+1)]`, which is not constant
  in `k`, so no normalisation makes `hslab` and `hspan` hold simultaneously for a fixed slab.

## What is still missing

The chain of `ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact` lives in `EuclideanSpace ℝ (Fin n)`
whereas the needle theorems live in `Fin (m+1) → ℝ`; a measure-preserving transport between the
two is **not** supplied here, so the end-to-end composition is stated in `Fin (m+1) → ℝ`.  That
is a purely technical mismatch, unchanged by this file.

## Honesty note

This file contains **no** `def`, `structure`, `class` or named `Prop` — only theorems proved
outright — and no theorem below takes the Localization Lemma, the isoperimetric inequality or
Dyer–Frieze as a hypothesis.
-/

open MeasureTheory Set Filter
open scoped ENNReal _root_.Topology


open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

/-! ### (G2c) for a shrinking slab -/

section GeneralPosition

variable {m : ℕ}

/-- **The localisation needle in general position, from a chain whose slab shrinks.**

`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_affine` with the fixed slab `{y | φ (y - a) ∈ [0,1]}`
replaced by the moving slabs `{y | φ (y - a) ∈ [l k, u k]}`, subject only to `l k → 0` and
`u k → 1`.  The transport is the frame of `ArlibCommunity.Foundations.Convex.exists_linearEquiv_frame` together with
`ArlibCommunity.Foundations.Convex.setIntegral_comp_affine` and `ArlibCommunity.Foundations.Convex.addHaar_preimage_affine`, exactly as in the fixed-slab
form: the Jacobian is a single positive constant and cancels out of both conclusions.

The integrands are asked to be *continuous*, not merely measurable: the point of the needle axis
at rescaled height `s` moves with `k`, and continuity is what makes the integrand follow it. -/
theorem exists_needleIntegral_eq_zero_and_pos_affine_shrinkingSlab (hm : m ≠ 0)
    {a v : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ} (hφv : φ v = 1)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDm : ∀ k, MeasurableSet (D k)) (hDfin : ∀ k, volume (D k) ≠ ⊤)
    (hDpos : ∀ k, 0 < volume (D k)) (hDbdd : ∀ k, ∃ R : ℝ, ∀ y ∈ D k, ‖y‖ ≤ R)
    {l u : ℕ → ℝ} (hlu : ∀ k, l k < u k)
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (l k) (u k))
    (hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - a) = t)
    (hl : Tendsto l atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 1))
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    {δ : ℕ → ℝ}
    (hδ₁ : ∀ k, ∀ y ∈ D k, |g₁ y - g₁ (a + φ (y - a) • v)| ≤ δ k)
    (hδ₂ : ∀ k, ∀ y ∈ D k, |g₂ y - g₂ (a + φ (y - a) • v)| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (a + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (a + t • v) := by
  obtain ⟨L, hLφ, hLcons⟩ := exists_linearEquiv_frame (m := m) (v := v) (φ := φ) hφv
  have hAm : Measurable fun x : Fin (m + 1) → ℝ => a + L x := measurable_affineSelfMap a L
  have hAc : Continuous fun x : Fin (m + 1) → ℝ => a + L x :=
    continuous_const.add
      (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)).continuous_of_finiteDimensional
  have hheight : ∀ x : Fin (m + 1) → ℝ, φ (a + L x - a) = x 0 := by
    intro x; rw [add_sub_cancel_left]; exact hLφ x
  have hAcons : ∀ t : ℝ, a + L (Fin.cons t (0 : Fin m → ℝ)) = a + t • v := by
    intro t; rw [hLcons t]
  have haxis : ∀ x : Fin (m + 1) → ℝ,
      a + L (Fin.cons (x 0) (0 : Fin m → ℝ)) = a + φ (a + L x - a) • v := by
    intro x; rw [hAcons, hheight]
  have hdet : LinearMap.det (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' L).ne_zero
  have hdpos : 0 < |(LinearMap.det (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)))⁻¹| :=
    abs_pos.mpr (inv_ne_zero hdet)
  have hvol : ∀ k, volume ((fun x => a + L x) ⁻¹' D k)
      = ENNReal.ofReal |(LinearMap.det (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)))⁻¹|
        * volume (D k) := fun k => addHaar_preimage_affine volume a L (hDm k)
  have hvolR : ∀ k, (volume ((fun x => a + L x) ⁻¹' D k)).toReal
      = |(LinearMap.det (L : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)))⁻¹|
        * (volume (D k)).toReal := by
    intro k; rw [hvol k, ENNReal.toReal_mul, ENNReal.toReal_ofReal hdpos.le]
  obtain ⟨W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_shrinkingSlab hm
    (C := fun k => (fun x => a + L x) ⁻¹' D k)
    (g₁ := fun x => g₁ (a + L x)) (g₂ := fun x => g₂ (a + L x))
    (fun k => convex_preimage_affine a L (hDconv k)) (fun k => hAm (hDm k))
    (fun k => by rw [hvol k]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hDfin k))
    (fun k => by
      rw [hvol k]
      exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hdpos).ne' (hDpos k).ne')
    (fun k t => by
      obtain ⟨R, hR⟩ := hDbdd k
      obtain ⟨R', hR'⟩ := exists_forall_abs_le_preimage_affine a L hR
      exact volume_slice_ne_top_of_forall_abs_le hR' t)
    hlu
    (fun k x hx => by rw [← hheight x]; exact hslab k _ hx)
    (fun k t ht => by
      obtain ⟨y, hy, hyt⟩ := hspan k t ht
      have hAx : a + L (L.symm (y - a)) = y := by
        rw [LinearEquiv.apply_symm_apply]; abel
      have hx0 : (L.symm (y - a) : Fin (m + 1) → ℝ) 0 = t := by
        rw [← hheight (L.symm (y - a)), hAx, hyt]
      refine ⟨Fin.tail (L.symm (y - a) : Fin (m + 1) → ℝ), ?_⟩
      show a + L (Fin.cons t (Fin.tail (L.symm (y - a) : Fin (m + 1) → ℝ))) ∈ D k
      rw [← hx0, Fin.cons_self_tail, hAx]
      exact hy)
    hl hu (hg₁.comp hAc) (hg₂.comp hAc) (fun x => hM₁ _) (fun x => hM₂ _)
    (fun k x hx => by rw [haxis x]; exact hδ₁ k _ hx)
    (fun k x hx => by rw [haxis x]; exact hδ₂ k _ hx) hδ0
    (fun k => by
      rw [setIntegral_comp_affine volume a L (hDm k) hg₁.measurable, hzero k, smul_zero])
    hεpos
    (fun k => by
      rw [setIntegral_comp_affine volume a L (hDm k) hg₂.measurable, smul_eq_mul, hvolR k]
      nlinarith [mul_le_mul_of_nonneg_left (hge k) hdpos.le])
  exact ⟨W, hW0, hWsupp, hWint, hWc, by simpa only [hAcons] using hW₁,
    by simpa only [hAcons] using hW₂⟩

end GeneralPosition

/-! ### The thinness bridge, for a shrinking slab -/

section Compact

variable {m : ℕ}

/-- **The localisation needle from a *compact* chain whose slab shrinks to the needle's.**

`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact` with the fixed slab replaced by the
moving one.  The transverse-thinness moduli are still supplied by
`ArlibCommunity.Foundations.Convex.exists_tendsto_transverse_modulus_pair`, which uses only compactness and the
finite-intersection property — no metric decay, and nothing about the slab. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_shrinkingSlab (hm : m ≠ 0)
    {a v : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ} (hφv : φ v = 1)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    {l u : ℕ → ℝ} (hlu : ∀ k, l k < u k)
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (l k) (u k))
    (hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - a) = t)
    (hl : Tendsto l atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 1))
    (haxis : ∀ y ∈ ⋂ k, D k, y = a + φ (y - a) • v)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ W : ℝ → ℝ, (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (a + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (a + t • v) := by
  obtain ⟨δ, hδ0, hδ₁, hδ₂⟩ :=
    exists_tendsto_transverse_modulus_pair hDcomp hDmono haxis hg₁ hg₂ hM₁ hM₂
  refine exists_needleIntegral_eq_zero_and_pos_affine_shrinkingSlab hm hφv hDconv
    (fun k => (hDcomp k).isClosed.measurableSet) (fun k => (hDcomp k).measure_lt_top.ne)
    hDpos (fun k => ?_) hlu hslab hspan hl hu hg₁ hg₂ hM₁ hM₂ hδ₁ hδ₂ hδ0 hzero hεpos hge
  exact isBounded_iff_forall_norm_le.mp (hDcomp k).isBounded

/-- **The localisation needle from a compact chain with a *collinear* limit body and a shrinking
slab.**

The `haxis` hypothesis of the previous theorem — "every point of `⋂ k, D k` lies on the
prescribed needle axis" — replaced by the purely geometric `Collinear ℝ (⋂ k, D k)`, which is what
`ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact` produces.  The axis is *produced*, not assumed:
`ArlibCommunity.Foundations.Convex.exists_axis_of_collinear` reads its base point and direction off the points of the
intersection at heights `0` and `1`, whose existence is Cantor's intersection theorem
(`ArlibCommunity.Foundations.Convex.exists_mem_iInter_height`) applied to the slab `[0,1]`, which is contained in every
`[l k, u k]` by `hl0` and `hu1`.

This is the shape a *shrinking* chain can satisfy: the bodies are only asked to lie in and span
the slab they actually occupy, and the sole normalisation is that the limit segment has unit
height. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab (hm : m ≠ 0)
    {a : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ}
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    {l u : ℕ → ℝ} (hl0 : ∀ k, l k ≤ 0) (hu1 : ∀ k, 1 ≤ u k)
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (l k) (u k))
    (hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - a) = t)
    (hl : Tendsto l atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 1))
    (hcol : Collinear ℝ (⋂ k, D k))
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), φ v = 1 ∧ (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  have hlu : ∀ k, l k < u k := fun k => lt_of_le_of_lt (hl0 k) (lt_of_lt_of_le one_pos (hu1 k))
  have hsub : ∀ k, Icc (0 : ℝ) 1 ⊆ Icc (l k) (u k) := fun k =>
    Icc_subset_Icc (hl0 k) (hu1 k)
  have hspan01 : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t :=
    fun k t ht => hspan k t (hsub k ht)
  obtain ⟨b, v, hb, hφv, haxis⟩ := exists_axis_of_collinear hDcomp hDmono hspan01 hcol
  have hshift : ∀ y : Fin (m + 1) → ℝ, φ (y - b) = φ (y - a) := by
    intro y; rw [map_sub, map_sub, hb]
  obtain ⟨W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_compact_shrinkingSlab
    hm hφv hDconv hDcomp hDmono hDpos hlu
    (fun k y hy => by rw [hshift]; exact hslab k y hy)
    (fun k t ht => by
      obtain ⟨y, hy, hyt⟩ := hspan k t ht
      exact ⟨y, hy, by rw [hshift]; exact hyt⟩)
    hl hu haxis hg₁ hg₂ hM₁ hM₂ hzero hεpos hge
  exact ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩

end Compact

/-! ### The acid test: a chain that shrinks in *every* direction -/

section ShrinkingBox

variable {m : ℕ}

/-- **Non-vacuity, with a genuinely shrinking chain.**

Every hypothesis of `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab` is
met simultaneously by the boxes

`D k = [-1/(k+1), 1 + 1/(k+1)] × [-1/(k+1), 1/(k+1)]^m`,

which shrink in **every** direction — including along the needle — and whose intersection is the
unit segment `[0,1] × {0}^m`, hence collinear.  They are convex, compact, decreasing and of
positive volume; the `k`-th one lies in and spans its own slab `[l k, u k]` with
`l k = -1/(k+1) ≤ 0`, `u k = 1 + 1/(k+1) ≥ 1`, `l k → 0`, `u k → 1`.

This is what the fixed-slab form `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear`
cannot accept: for these boxes the height range `[-1/(k+1), 1 + 1/(k+1)]` genuinely varies with
`k`, so no affine normalisation of the height makes `hslab` and `hspan` hold for one fixed slab
at every stage — which is exactly the obstruction recorded as item (E).  The witness of
`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear_box` has to keep the extent along the
needle constant at `[0,1]` for precisely this reason.

The profile that comes out is nonzero, since its integral is positive. -/
theorem exists_needleIntegral_eq_zero_and_pos_shrinking_box (hm : m ≠ 0) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ),
      (LinearMap.proj (0 : Fin (m + 1)) : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ) v = 1 ∧ (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      0 < ∫ t : ℝ, W t * (1 : ℝ) := by
  classical
  set ρ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hρ
  have hρpos : ∀ k, 0 < ρ k := fun k => by rw [hρ]; positivity
  have hρanti : ∀ k, ρ (k + 1) ≤ ρ k := by
    intro k
    rw [hρ]
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    exact one_div_le_one_div_of_le h1 h2
  set l : ℕ → ℝ := fun k => -ρ k with hldef
  set u : ℕ → ℝ := fun k => 1 + ρ k with hudef
  set D : ℕ → Set (Fin (m + 1) → ℝ) := fun k =>
    univ.pi fun i => if i = 0 then Icc (l k) (u k) else Icc (-ρ k) (ρ k) with hD
  have hDcomp : ∀ k, IsCompact (D k) := by
    intro k
    refine isCompact_univ_pi fun i => ?_
    by_cases hi : i = 0
    · rw [if_pos hi]; exact isCompact_Icc
    · rw [if_neg hi]; exact isCompact_Icc
  have hDconv : ∀ k, Convex ℝ (D k) := by
    intro k
    refine convex_pi fun i _ => ?_
    by_cases hi : i = 0
    · rw [if_pos hi]; exact convex_Icc _ _
    · rw [if_neg hi]; exact convex_Icc _ _
  have hDmono : ∀ k, D (k + 1) ⊆ D k := by
    intro k y hy
    refine Set.mem_univ_pi.mpr fun i => ?_
    have hyi := Set.mem_univ_pi.mp hy i
    have hr := hρanti k
    by_cases hi : i = 0
    · rw [if_pos hi] at hyi ⊢
      exact Set.Icc_subset_Icc (by rw [hldef]; simp only; linarith)
        (by rw [hudef]; simp only; linarith) hyi
    · rw [if_neg hi] at hyi ⊢
      exact Set.Icc_subset_Icc (by linarith) (by linarith) hyi
  have hDpos : ∀ k, 0 < volume (D k) := by
    intro k
    have hr := hρpos k
    rw [hD]
    simp only
    rw [volume_pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    by_cases hi : i = 0
    · rw [if_pos hi, Real.volume_Icc]
      refine (ENNReal.ofReal_pos.mpr ?_).ne'
      rw [hldef, hudef]; simp only; linarith
    · rw [if_neg hi, Real.volume_Icc]
      exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  set φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0 with hφ
  have hslab : ∀ k, ∀ y ∈ D k, φ (y - 0) ∈ Icc (l k) (u k) := by
    intro k y hy
    have h0 := Set.mem_univ_pi.mp hy 0
    rw [if_pos rfl] at h0
    simpa [hφ] using h0
  have hspan : ∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - 0) = t := by
    intro k t ht
    refine ⟨fun i => if i = 0 then t else 0, Set.mem_univ_pi.mpr fun i => ?_, by simp [hφ]⟩
    by_cases hi : i = 0
    · rw [if_pos hi, if_pos hi]; exact ht
    · rw [if_neg hi, if_neg hi]
      exact ⟨by linarith [hρpos k], (hρpos k).le⟩
  have hρ0 : Tendsto ρ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto l atTop (𝓝 0) := by simpa [hldef] using hρ0.neg
  have hu : Tendsto u atTop (𝓝 1) := by
    simpa [hudef] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add hρ0
  have hl0 : ∀ k, l k ≤ 0 := fun k => by rw [hldef]; simp only; linarith [hρpos k]
  have hu1 : ∀ k, 1 ≤ u k := fun k => by rw [hudef]; simp only; linarith [hρpos k]
  -- the intersection is the unit segment, hence collinear
  have hzeroCoord : ∀ y ∈ ⋂ k, D k, ∀ i : Fin (m + 1), i ≠ 0 → y i = 0 := by
    intro y hy i hi
    have hy' : ∀ k, y ∈ D k := fun k => Set.mem_iInter.mp hy k
    by_contra hne
    have habs : 0 < |y i| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt habs
    have hmem := Set.mem_univ_pi.mp (hy' n) i
    rw [if_neg hi] at hmem
    have : |y i| ≤ ρ n := abs_le.mpr ⟨hmem.1, hmem.2⟩
    rw [hρ] at this
    simp only at this
    linarith
  have hcol : Collinear ℝ (⋂ k, D k) := by
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨0, Pi.single 0 1, fun y hy => ⟨y 0, ?_⟩⟩
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi, hzeroCoord y hy i hi]
  obtain ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, -, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab hm (a := 0) (φ := φ)
      hDconv hDcomp hDmono hDpos hl0 hu1 hslab hspan hl hu hcol
      (g₁ := fun _ => (0 : ℝ)) (g₂ := fun _ => (1 : ℝ)) continuous_const continuous_const
      (M := 1) (fun _ => by norm_num) (fun _ => by norm_num)
      (fun k => integral_zero _ _) (ε := 1) one_pos
      (fun k => by rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, one_mul])
  exact ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, hW₂⟩

end ShrinkingBox

end ArlibCommunity.Foundations.Convex

/-! ### Axiom audit -/

#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_affine_shrinkingSlab
#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact_shrinkingSlab
#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab
#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_shrinking_box

end

section
/-!
# Every nondegenerate compact convex chain satisfies the shrinking-slab hypotheses

`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab` asks the `k`-th body to
lie in and span its own slab `[l k, u k]`, with `l k ≤ 0 ≤ 1 ≤ u k` and `l k → 0`, `u k → 1`.
This file shows those hypotheses are **not** a restriction on the chain: they hold for *every*
decreasing chain of compact convex bodies whose intersection contains two distinct points, once
the height functional has been normalised so that the intersection has height range exactly
`[0,1]`.

That is the difference from the fixed slab of `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact`,
which asks the height range of **every** `D k` to be `[0,1]` and hence forces it to be constant
along the chain (`ArlibCommunity.Foundations.Convex.exists_mem_iInter_height`) — item **(E)** of
`ArlibCommunity.Foundations.Convex.Localization.Analysis.LocalizationAssembly`.

## Main results

* `ArlibCommunity.Foundations.Convex.exists_slab_of_compact_chain` — the slabs.  `l k` and `u k` are the minimum and maximum
  of the height functional on `D k`; `hslab` and `hspan` are then automatic (compactness for the
  extrema, the intermediate value theorem along a chord for the spanning), and `l k → 0`,
  `u k → 1` follow from the finite-intersection property
  (`ArlibCommunity.Foundations.Convex.eventually_subset_of_antitone_isCompact`) — no metric decay and no rate.
* `ArlibCommunity.Foundations.Convex.exists_unitHeight_functional` — the normalisation.  For a compact convex set with two
  distinct points there is a base point in it and a linear functional for which its height range
  is exactly `[0,1]`.
* `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact_chain` — **the composition**: from a
  decreasing chain of compact convex bodies of positive volume, with collinear intersection
  containing two distinct points, and the two localisation invariants `∫_{D k} g₁ = 0` and
  `ε · vol (D k) ≤ ∫_{D k} g₂`, the two conclusions of the equality-refined Localization Lemma,
  with a nonnegative profile whose `1/m`-th power is concave.

## What the composition still needs from the caller

Two things, both stated as explicit hypotheses rather than hidden:

* **Nondegeneracy.**  The intersection must contain two distinct points.  A chain whose
  intersection is a single point produces a degenerate needle, for which the conclusion as stated
  (a profile on `(0,1)`) is not the right shape.  `ArlibCommunity.Foundations.Convex.le_diam_of_sign_separated` shows the
  intersection is forced to be nondegenerate when the positive parts of `g₁` and `g₂` are
  separated by a slab, but that is a hypothesis on the data, not a consequence of the chain.
* **The ambient type.**  `ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact` produces its chain in
  `EuclideanSpace ℝ (Fin n)` while the needle theorems live in `Fin (m+1) → ℝ`.  A
  measure-preserving transport between the two is **not** supplied here.

## Honesty note

This file contains **no** `def`, `structure`, `class` or named `Prop` — only theorems proved
outright — and no theorem below takes the Localization Lemma, the isoperimetric inequality or
Dyer–Frieze as a hypothesis.
-/

open MeasureTheory Set Filter
open scoped ENNReal _root_.Topology


open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.Convex

/-! ### The height range of a chain of compact convex bodies -/

section HeightRange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The slabs of a compact convex chain, and their shrinking.**

Let `D` be a decreasing sequence of compact convex bodies, `a` a point of their intersection, and
`φ` a linear functional for which the intersection has height range exactly `[0,1]` (heights
measured by `φ (· - a)`).  Then, taking `l k` and `u k` to be the minimum and maximum of the
height on `D k`:

* every `D k` lies in the slab `[l k, u k]` and *spans* it — the first by definition of the
  extrema, the second by the intermediate value theorem along the chord joining the two extremal
  points, which lies in `D k` by convexity;
* `l k ≤ 0 ≤ 1 ≤ u k`, because `a` and the point of height `1` belong to every `D k`;
* `l k → 0` and `u k → 1`.

The last item is where the chain's shrinking is used, and it uses only the finite-intersection
property: `{y | φ (y - a) ∈ (-ε, 1 + ε)}` is an open set containing `⋂ k, D k`, so
`ArlibCommunity.Foundations.Convex.eventually_subset_of_antitone_isCompact` puts every late `D k` inside it.  No metric
decay, no Hausdorff convergence and no rate. -/
theorem exists_slab_of_compact_chain {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDconv : ∀ k, Convex ℝ (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    {a : E} {φ : E →ₗ[ℝ] ℝ} (ha : a ∈ ⋂ k, D k)
    (hone : ∃ q ∈ ⋂ k, D k, φ (q - a) = 1)
    (hIle : ∀ y ∈ ⋂ k, D k, φ (y - a) ∈ Icc (0 : ℝ) 1) :
    ∃ l u : ℕ → ℝ, (∀ k, l k ≤ 0) ∧ (∀ k, 1 ≤ u k) ∧
      (∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (l k) (u k)) ∧
      (∀ k, ∀ t ∈ Icc (l k) (u k), ∃ y ∈ D k, φ (y - a) = t) ∧
      Tendsto l atTop (𝓝 0) ∧ Tendsto u atTop (𝓝 1) := by
  classical
  set h : E → ℝ := fun y => φ (y - a) with hhdef
  have hcont : Continuous h :=
    (φ.continuous_of_finiteDimensional).comp (continuous_id.sub continuous_const)
  obtain ⟨q, hqI, hq1⟩ := hone
  have haD : ∀ k, a ∈ D k := fun k => Set.mem_iInter.mp ha k
  have hqD : ∀ k, q ∈ D k := fun k => Set.mem_iInter.mp hqI k
  have himg : ∀ k, IsCompact (h '' D k) := fun k => (hDcomp k).image hcont
  have himgne : ∀ k, (h '' D k).Nonempty := fun k => ⟨h a, ⟨a, haD k, rfl⟩⟩
  refine ⟨fun k => sInf (h '' D k), fun k => sSup (h '' D k), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    [skip; skip; skip; skip; skip; skip]
  all_goals {
    have hlmem : ∀ k, sInf (h '' D k) ∈ h '' D k := fun k => (himg k).sInf_mem (himgne k)
    have humem : ∀ k, sSup (h '' D k) ∈ h '' D k := fun k => (himg k).sSup_mem (himgne k)
    have hbddB : ∀ k, BddBelow (h '' D k) := fun k => (himg k).bddBelow
    have hbddA : ∀ k, BddAbove (h '' D k) := fun k => (himg k).bddAbove
    have hslab : ∀ k, ∀ y ∈ D k, h y ∈ Icc (sInf (h '' D k)) (sSup (h '' D k)) := fun k y hy =>
      ⟨csInf_le (hbddB k) ⟨y, hy, rfl⟩, le_csSup (hbddA k) ⟨y, hy, rfl⟩⟩
    have hha : h a = 0 := by simp [hhdef]
    have hbound : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k, N ≤ k →
        -ε < sInf (h '' D k) ∧ sSup (h '' D k) < 1 + ε := by
      intro ε hε
      have hopen : IsOpen (h ⁻¹' Ioo (-ε) (1 + ε)) := isOpen_Ioo.preimage hcont
      have hsub : (⋂ k, D k) ⊆ h ⁻¹' Ioo (-ε) (1 + ε) := by
        intro y hy
        obtain ⟨h1, h2⟩ := hIle y hy
        exact ⟨by linarith, by linarith⟩
      obtain ⟨N, hN⟩ := eventually_subset_of_antitone_isCompact hDcomp hDmono hopen hsub
      refine ⟨N, fun k hk => ?_⟩
      obtain ⟨p, hp, hpl⟩ := hlmem k
      obtain ⟨r, hr, hru⟩ := humem k
      exact ⟨by rw [← hpl]; exact (hN k hk hp).1, by rw [← hru]; exact (hN k hk hr).2⟩
    first
      | -- `l k ≤ 0`
        exact fun k => hha ▸ (hslab k a (haD k)).1
      | -- `1 ≤ u k`
        exact fun k => hq1 ▸ (hslab k q (hqD k)).2
      | -- `hslab`
        exact hslab
      | -- `hspan`
        (intro k t ht
         obtain ⟨p, hp, hpl⟩ := hlmem k
         obtain ⟨r, hr, hru⟩ := humem k
         have hfmem : ∀ s ∈ Icc (0 : ℝ) 1, p + s • (r - p) ∈ D k := by
           intro s hs
           have heq : p + s • (r - p) = (1 - s) • p + s • r := by module
           rw [heq]
           exact hDconv k hp hr (by linarith [hs.2]) hs.1 (by ring)
         have hfc : ContinuousOn (fun s : ℝ => h (p + s • (r - p))) (Icc 0 1) :=
           (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
         have h0 : h (p + (0 : ℝ) • (r - p)) = sInf (h '' D k) := by simpa using hpl
         have h1 : h (p + (1 : ℝ) • (r - p)) = sSup (h '' D k) := by
           simpa [add_sub_cancel] using hru
         have hiv := intermediate_value_Icc (zero_le_one (α := ℝ)) hfc
         rw [h0, h1] at hiv
         obtain ⟨s, hs, hsv⟩ := hiv ht
         exact ⟨p + s • (r - p), hfmem s hs, hsv⟩)
      | -- `l k → 0`
        (rw [Metric.tendsto_atTop]
         intro ε hε
         obtain ⟨N, hN⟩ := hbound ε hε
         refine ⟨N, fun k hk => ?_⟩
         have h1 := (hN k hk).1
         have h2 : sInf (h '' D k) ≤ 0 := hha ▸ (hslab k a (haD k)).1
         rw [Real.dist_eq, sub_zero, abs_of_nonpos h2]
         linarith)
      | -- `u k → 1`
        (rw [Metric.tendsto_atTop]
         intro ε hε
         obtain ⟨N, hN⟩ := hbound ε hε
         refine ⟨N, fun k hk => ?_⟩
         have h1 := (hN k hk).2
         have h2 : (1 : ℝ) ≤ sSup (h '' D k) := hq1 ▸ (hslab k q (hqD k)).2
         rw [Real.dist_eq, abs_of_nonneg (by linarith)]
         linarith) }

end HeightRange

/-! ### Normalising the limit body to unit height -/

section Normalisation

variable {m : ℕ}

/-- **A compact convex set with two distinct points has unit height in a suitable frame.**

There is a base point `a` of `S` and a linear functional `φ` for which the height range
`φ '' (S - a)` is exactly `[0,1]`: take any coordinate `j` in which `q - p` does not vanish,
scale the `j`-th projection so that it sends `q - p` to `1`, then translate the base point to the
minimiser and rescale by the total height, which is at least `1` and hence nonzero.

This is the only normalisation the shrinking-slab needle theorem needs, and it is available for
*any* nondegenerate compact convex limit body — no collinearity is used here. -/
theorem exists_unitHeight_functional {S : Set (Fin (m + 1) → ℝ)} (hScomp : IsCompact S)
    {p q : Fin (m + 1) → ℝ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    ∃ (a : Fin (m + 1) → ℝ) (φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ), a ∈ S ∧
      (∃ z ∈ S, φ (z - a) = 1) ∧ ∀ y ∈ S, φ (y - a) ∈ Icc (0 : ℝ) 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin (m + 1), q j - p j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hpq (funext fun j => by have := hcon j; linarith)
  set ψ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ := (q j - p j)⁻¹ • LinearMap.proj j with hψdef
  have hψapp : ∀ y : Fin (m + 1) → ℝ, ψ y = (q j - p j)⁻¹ * y j := fun y => rfl
  have hψw : ψ (q - p) = 1 := by
    rw [hψapp]
    simp only [Pi.sub_apply]
    exact inv_mul_cancel₀ hj
  have hcontψ : Continuous fun y : Fin (m + 1) → ℝ => ψ y :=
    ψ.continuous_of_finiteDimensional
  have himg : IsCompact ((fun y => ψ y) '' S) := hScomp.image hcontψ
  have himgne : ((fun y => ψ y) '' S).Nonempty := ⟨ψ p, ⟨p, hp, rfl⟩⟩
  obtain ⟨a, haS, hamin⟩ := himg.sInf_mem himgne
  obtain ⟨z, hzS, hzmax⟩ := himg.sSup_mem himgne
  have hamin' : ψ a = sInf ((fun y => ψ y) '' S) := hamin
  have hzmax' : ψ z = sSup ((fun y => ψ y) '' S) := hzmax
  have hle : ∀ y ∈ S, ψ a ≤ ψ y ∧ ψ y ≤ ψ z := by
    intro y hy
    constructor
    · rw [hamin']; exact csInf_le himg.bddBelow ⟨y, hy, rfl⟩
    · rw [hzmax']; exact le_csSup himg.bddAbove ⟨y, hy, rfl⟩
  have hgap : (1 : ℝ) ≤ ψ z - ψ a := by
    have h1 := (hle p hp).1
    have h2 := (hle q hq).2
    have h3 : ψ q - ψ p = 1 := by rw [← hψw, map_sub]
    linarith
  have hgap0 : (0 : ℝ) < ψ z - ψ a := by linarith
  refine ⟨a, (ψ z - ψ a)⁻¹ • ψ, haS, ⟨z, hzS, ?_⟩, fun y hy => ?_⟩
  · show (ψ z - ψ a)⁻¹ * ψ (z - a) = 1
    rw [map_sub]
    exact inv_mul_cancel₀ hgap0.ne'
  · obtain ⟨h1, h2⟩ := hle y hy
    show (ψ z - ψ a)⁻¹ * ψ (y - a) ∈ Icc (0 : ℝ) 1
    rw [map_sub]
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hgap0.le) (by linarith)
    · rw [inv_mul_le_iff₀ hgap0]
      linarith

end Normalisation

/-! ### The composition -/

section Composition

variable {m : ℕ}

/-- **The localisation needle from an arbitrary nondegenerate compact convex chain.**

Every hypothesis of `ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab`
about the *slab* is discharged here: the height functional is produced by
`ArlibCommunity.Foundations.Convex.exists_unitHeight_functional` and the slabs by `ArlibCommunity.Foundations.Convex.exists_slab_of_compact_chain`.  What
is left to ask of the chain is exactly what a localisation chain provides —

* decreasing compact convex bodies of positive volume (`ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact`),
* a collinear intersection (same),
* the two mass invariants `∫_{D k} g₁ = 0` and `ε · vol (D k) ≤ ∫_{D k} g₂`
  (`ArlibCommunity.Foundations.Convex.exists_flat_cut_chain_collinear_compact_ge`),

— together with **nondegeneracy** of the limit body, which is a hypothesis on the data and not a
consequence of the chain (see the module docstring).

No hypothesis relates the height range of `D k` to that of `D 0`: the chain may shrink in every
direction, including along the needle.

The profile is delivered **supported in `[0,1]` and integrable**, not merely nonnegative and
concave-to-the-`1/m`: both come from the origin
`ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_shrinkingSlab` and are threaded through unchanged,
since every step of the transport reuses the *same* `W`.  Consumers need both — a Bochner integral
of a non-integrable nonnegative function is `0`, not `+∞`, so a monotone comparison of needle
masses is false without integrability, and `∫ t : ℝ` is not `∫ t in [α,β]` without the support. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_compact_chain (hm : m ≠ 0)
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDcomp : ∀ k, IsCompact (D k))
    (hDconv : ∀ k, Convex ℝ (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k)) (hcol : Collinear ℝ (⋂ k, D k))
    {p q : Fin (m + 1) → ℝ} (hp : p ∈ ⋂ k, D k) (hq : q ∈ ⋂ k, D k) (hpq : p ≠ q)
    {g₁ g₂ : (Fin (m + 1) → ℝ) → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {M : ℝ} (hM₁ : ∀ x, |g₁ x| ≤ M) (hM₂ : ∀ x, |g₂ x| ≤ M)
    (hzero : ∀ k, (∫ y in D k, g₁ y) = 0)
    {ε : ℝ} (hεpos : 0 < ε) (hge : ∀ k, ε * (volume (D k)).toReal ≤ ∫ y in D k, g₂ y) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ), (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      (∫ t : ℝ, W t * g₁ (b + t • v)) = 0 ∧
      0 < ∫ t : ℝ, W t * g₂ (b + t • v) := by
  have hIcomp : IsCompact (⋂ k, D k) :=
    (hDcomp 0).of_isClosed_subset (isClosed_iInter fun k => (hDcomp k).isClosed)
      (Set.iInter_subset _ 0)
  obtain ⟨a, φ, haS, hone, hIle⟩ := exists_unitHeight_functional hIcomp hp hq hpq
  obtain ⟨l, u, hl0, hu1, hslab, hspan, hl, hu⟩ :=
    exists_slab_of_compact_chain hDcomp hDconv hDmono haS hone hIle
  obtain ⟨b, v, W, -, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_collinear_shrinkingSlab hm hDconv hDcomp hDmono
      hDpos hl0 hu1 hslab hspan hl hu hcol hg₁ hg₂ hM₁ hM₂ hzero hεpos hge
  exact ⟨b, v, W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩

end Composition

end ArlibCommunity.Foundations.Convex

/-! ### Axiom audit -/

#print axioms ArlibCommunity.Foundations.Convex.exists_slab_of_compact_chain
#print axioms ArlibCommunity.Foundations.Convex.exists_unitHeight_functional
#print axioms ArlibCommunity.Foundations.Convex.exists_needleIntegral_eq_zero_and_pos_of_compact_chain

end
