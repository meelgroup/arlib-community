/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.SharpIsoperimetry
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LogisticIso
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.KLS97Lemma38
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.ConcaveProfileIso

/-!
# `thm:iso` for a **concave** needle profile, with only the Localization Lemma left

`Arlib.gaussianRestricted_isoperimetry` (`Arlib/Convexity/SharpIsoperimetry.lean:320`) proves
Cousins–Vempala's Theorem 3.4 (`1409.6011/vol3_journal.tex:467`) at the sharp constant `d/σ`
from **four** residual `∀`-binders: `hloc`, `hcombinatorial`, `h1d1`, `h1d2`.  Three of those
four are now theorems of this repository.  This file restates the result so that **`hloc` is the
only residual binder**, and — more importantly — restates `hloc` in the shape the localization
stack of this repository actually delivers.

## Main results

* `Arlib.oneDimCoeff_mul_le'`, `Arlib.le_oneDimCoeff_of_sep'` — the `max` step of
  `Arlib.oneDimCoeff_mul_le` / `Arlib.le_oneDimCoeff_of_sep`, with the `(1d-2)` coefficient a
  parameter `c₂` instead of the paper's hard-wired `ln 2`.
* `Arlib.gaussianRestricted_isoperimetry_concave_of_oneDim` — `thm:iso` for a concave profile,
  with `hcombinatorial` and `h1d1` discharged and `(1d-2)` still a binder at coefficient `c₂/σ`.
* `Arlib.gaussianRestricted_isoperimetry_concave` — **the theorem.**  `hloc` is the only
  residual binder.
* `Arlib.gaussianRestricted_isoperimetry_concave_witness` — the non-vacuity witness, which
  satisfies **every** hypothesis, `hloc` included.

## What is proved here, relative to `Arlib.gaussianRestricted_isoperimetry`

Three of the four external inputs are discharged, by theorems of this repository:

1. **`hcombinatorial`** ← `Arlib.oneDim_partition` (`Arlib/Convexity/LogisticIso.lean:549`).
   The match is **verbatim**: same binders, same order, no extra hypothesis.
2. **`h1d1`** ← `Arlib.kls38_concave` (`Arlib/Convexity/KLS97Lemma38.lean:1241`).  Not
   `Arlib.kls38_affine`: see "the profile is concave" below.  The binder shape differs from
   `h1d1` as printed in `Arlib.gaussianRestricted_isoperimetry` — the affine witness
   `∃ c₀ c₁, ∀ t, l t = c₀ + c₁ * t` is replaced by `ConcaveOn ℝ (Set.Icc α β) l` — and
   `kls38_concave` is applied directly at the needle rather than through a binder.
3. **`h1d2`** ← `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`
   (`Arlib/Convexity/ConcaveProfileIso.lean:631`), **at a weaker constant**; see next.

## The constant: `1/(2√3)` in place of `ln 2` — quoted with the result

Cousins–Vempala's `(1d-2)` (`vol3_journal.tex:501`) carries the coefficient
`\iso = ln 2 ≈ 0.693`.  What this repository proves —
`Arlib.oneDim_isoperimetry_gaussianFactor_unconditional`, via Brascamp–Lieb — is the same
inequality at `1/(2√3) ≈ 0.2887`, which is **strictly weaker**.  The `(1d-2)` coefficient is
therefore a *parameter* `c₂` of `Arlib.gaussianRestricted_isoperimetry_concave_of_oneDim`, and
`Arlib.gaussianRestricted_isoperimetry_concave` instantiates `c₂ := 1/(2√3)`.

**The cost, stated plainly.**  The conclusion is unchanged — still the sharp `d/σ`.  What
weakens is the *metric branch of the separation hypothesis*: the threshold is

  `2√3·d ≈ 3.464·d`   instead of   `d / ln 2 ≈ 1.443·d`,

a constant factor `2√3·ln 2 ≈ 2.401`.  So the theorem here applies to fewer partitions than the
printed one: `S₁` and `S₂` must be `2.401×` further apart before the metric branch fires.  The
density branch `4(d/σ)√n ≤ d_h(u,v)` is untouched.  Downstream, an application that wants a
given metric separation must shrink `d` by that factor, costing a constant factor in every
conductance bound derived from `thm:iso` — and nothing more.  Recovering `ln 2` needs a sharper
`(1d-2)`; `Arlib.Convexity.ConcaveProfileIso` does not have it.

## The profile is concave, and that is the point

`hloc` as printed in `Arlib.gaussianRestricted_isoperimetry` asks the Localization Lemma to
deliver an **affine** profile `(c₀ + c₁t)^{n−1}`.  This repository's localization stack does not
deliver that, and `Arlib.exists_convex_slice_profile_not_affine`
(`Arlib/Convexity/LocalizationLimit.lean`) **refutes** the concave-to-affine upgrade.  What
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear`
(`Arlib/Convexity/LocalizationClosed.lean:376`) produces is a nonnegative `W` with `W^{1/m}`
concave; writing `l := W^{1/m}` that is exactly a nonnegative **concave** `l` with profile
`l^{n−1}`, which is the shape `hloc` carries here.

Everything downstream survives the change:

* `(1d-1)` — `Arlib.kls38_concave` is `(1d-1)` for a concave profile.  Its docstring records
  that affineness of `ℓ` is never used in the proof.
* `(1d-2)` — needs the needle density to be log-concave.  `l ≥ 0` concave makes `l^{n−1}`
  log-concave (`Arlib.logConcaveOn_pow_of_concaveOn`), hence `l^{n−1}·f∘γ` log-concave
  (`Arlib.LogConcaveOn.mul`), which is what
  `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional` consumes.  Affineness was never used
  there either.

The needle is still **arclength**-parameterised (`‖e‖ = 1`, parameter interval `[α,β]`), as in
`Arlib.gaussianRestricted_isoperimetry`; that is what makes the Gaussian factor along the needle
a one-dimensional Gaussian *of the same `σ`* (`Arlib.gaussian_needleMap`) and hence what makes
the `σ` in `c₂/σ` the same `σ` as in the conclusion's `d/σ`.

## What is assumed

Exactly one thing: **`hloc`, the Localization Lemma** of Lovász–Simonovits (KLS 1995,
Corollary 2.4), applied to `g₁ = 1_{S₁}h − A·h` and `g₂ = (d/σ)A·1_{S₂}h − 1_{S₃}h`
(`vol3_journal.tex:479–493`), in the concave-profile, arclength-parameterised form described
above.  It is a plain `∀`-binder of
`Arlib.gaussianRestricted_isoperimetry_concave` — there is no `def … : Prop` packaging it, and
no `axiom`.  Its status in this repository is the subject of
`Arlib.Convexity.LocalizationAssembly` (residuals **(A)** transverse thinness and **(B)/(G2c)**
the affine change of coordinates, listed in that file's docstring) and
`Arlib.Convexity.LocalizationClosed`.

The `σ`-corrected density branch of the separation hypothesis is inherited unchanged from
`Arlib.gaussianRestricted_isoperimetry`; see that file's docstring, "Two discrepancies with the
printed paper", for why the printed `d_h(u,v) ≥ 4d√n` cannot be right at general `σ` and why the
paper's own downstream use survives the correction.

## Non-vacuity

`Arlib.gaussianRestricted_isoperimetry_concave_witness` exhibits data satisfying **every**
hypothesis of `Arlib.gaussianRestricted_isoperimetry_concave`, `hloc` included, with the
left-hand side `(d/σ)·(∫_{S₁}h)(∫_{S₂}h)` **strictly positive**.  It strengthens
`Arlib.gaussianRestricted_isoperimetry_witness`, which leaves `hloc` out: here `d` is chosen
small enough (`d ≤ (∫h)(∫_{S₃}h)/((∫_{S₁}h)(∫_{S₂}h))`, and `d ≤ 1/8` so that the metric branch
still fires) that `hloc`'s antecedent is *provably* contradictory, so `hloc` holds — vacuously,
but verifiably, which is what a witness has to show.

## No rate claim

Nothing here says, or implies, that any algorithm runs in polynomial time.  This file removes
three of four hypotheses from a conditional reduction; the remaining one, localization, is the
hard one.

## References

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian Volume*,
§3 (`1409.6011/vol3_journal.tex:404–508`).

Kannan, Lovász and Simonovits, *Random walks and an `O*(n⁵)` volume algorithm for convex
bodies*, Random Structures & Algorithms **11** (1997), Lemma 3.8.
-/

open MeasureTheory Set

namespace Arlib

/-! ### The `max` step, with the `(1d-2)` coefficient a parameter -/

section OneDimCombination

/-- **`Arlib.oneDimCoeff_mul_le` with the `(1d-2)` coefficient a parameter.**

Identical to `Arlib.oneDimCoeff_mul_le` except that the paper's hard-wired `ln 2` is replaced by
an arbitrary `c₂`; nothing in the argument depends on its value.  This is what lets
`Arlib.gaussianRestricted_isoperimetry_concave` run at the `1/(2√3)` that
`Arlib.oneDim_isoperimetry_gaussianFactor_unconditional` actually proves. -/
theorem oneDimCoeff_mul_le' {n : ℕ} {σ c₂ Dh ρ L R I Mid : ℝ} (hn : 0 < n)
    (h1d1 : Dh * (L * R) ≤ 4 * Real.sqrt n * (I * Mid))
    (h1d2 : c₂ / σ * ρ * (L * R) ≤ I * Mid) :
    max (Dh / (4 * Real.sqrt n)) (c₂ / σ * ρ) * (L * R) ≤ I * Mid := by
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsq4 : 0 < 4 * Real.sqrt n := by positivity
  rcases max_cases (Dh / (4 * Real.sqrt n)) (c₂ / σ * ρ) with ⟨he, -⟩ | ⟨he, -⟩
  · rw [he, div_mul_eq_mul_div, div_le_iff₀ hsq4]
    have hcomm : I * Mid * (4 * Real.sqrt n) = 4 * Real.sqrt n * (I * Mid) := by ring
    rw [hcomm]
    exact h1d1
  · rw [he]
    exact h1d2

/-- **`Arlib.le_oneDimCoeff_of_sep` with the `(1d-2)` coefficient a parameter.**

The separation hypothesis's metric branch reads `d / c₂ ≤ ‖u − v‖` rather than the paper's
`d / ln 2 ≤ ‖u − v‖`; all that is used about `c₂` is `0 < c₂`. -/
theorem le_oneDimCoeff_of_sep' {n : ℕ} {σ d ρ Dh c₂ : ℝ} (hn : 0 < n) (hσ : 0 < σ)
    (hc₂ : 0 < c₂) (hsep : d / c₂ ≤ ρ ∨ 4 * (d / σ) * Real.sqrt n ≤ Dh) :
    d / σ ≤ max (Dh / (4 * Real.sqrt n)) (c₂ / σ * ρ) := by
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  rcases hsep with hmetric | hdens
  · refine le_max_of_le_right ?_
    have hrw : d / σ = c₂ / σ * (d / c₂) := by field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hmetric (by positivity)
  · refine le_max_of_le_left ?_
    rw [le_div_iff₀ (by positivity)]
    calc d / σ * (4 * Real.sqrt n) = 4 * (d / σ) * Real.sqrt n := by ring
      _ ≤ Dh := hdens

end OneDimCombination

/-! ### `thm:iso` for a concave profile, with `(1d-2)` still a binder -/

section MainGeneric

variable {n : ℕ}

/-- **Cousins–Vempala's `thm:iso` for a concave needle profile, with `hcombinatorial` and
`(1d-1)` discharged.**

Same conclusion as `Arlib.gaussianRestricted_isoperimetry` — `(d/σ)·π(S₁)π(S₂) ≤ π(S₃)` in the
division-free form — but:

* the localization binder `hloc` delivers a **concave** profile `l ≥ 0` with density
  `l^{n−1}·h∘γ`, not the affine `(c₀ + c₁t)^{n−1}` of the printed proof.  This is the shape
  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear` produces (there as `W` with
  `W^{1/m}` concave; put `l := W^{1/m}`), and
  `Arlib.exists_convex_slice_profile_not_affine` shows the affine upgrade is false;
* `hcombinatorial` is discharged by `Arlib.oneDim_partition`;
* `(1d-1)` is discharged by `Arlib.kls38_concave`, which is exactly `(1d-1)` for a concave
  profile;
* `(1d-2)` remains a binder, at an arbitrary coefficient `c₂/σ`, and the metric branch of the
  separation hypothesis reads `d / c₂ ≤ ‖u − v‖`.  `c₂ = ln 2` is the paper's value;
  `Arlib.gaussianRestricted_isoperimetry_concave` instantiates the `c₂ = 1/(2√3)` that
  `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional` proves. -/
theorem gaussianRestricted_isoperimetry_concave_of_oneDim (hn : 0 < n) {σ d c₂ : ℝ} (hσ : 0 < σ)
    (hc₂ : 0 < c₂)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / c₂ ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v)
    -- **(L)** The Localization Lemma, with a **concave** profile; see the module docstring.
    (hloc : ∀ A : ℝ, 0 < A →
      (∫ x in S₁, h x) = A * ∫ x, h x →
      (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (l : ℝ → ℝ) (α β : ℝ),
        ‖e‖ = 1 ∧ α ≤ β ∧ (∀ t ∈ Set.Icc α β, 0 ≤ l t) ∧
        ConcaveOn ℝ (Set.Icc α β) l ∧
        IntervalIntegrable
          (fun t => l t ^ (n - 1) * h (needleMap p e t)) volume α β ∧
        (∫ t in needleMap p e ⁻¹' S₁ ∩ Set.Icc α β,
            l t ^ (n - 1) * h (needleMap p e t))
          = A * ∫ t in α..β, l t ^ (n - 1) * h (needleMap p e t) ∧
        (∫ t in needleMap p e ⁻¹' S₃ ∩ Set.Icc α β,
            l t ^ (n - 1) * h (needleMap p e t))
          < d / σ * A * ∫ t in needleMap p e ⁻¹' S₂ ∩ Set.Icc α β,
              l t ^ (n - 1) * h (needleMap p e t))
    -- **(1d-2)** `vol3_journal.tex:501`, at coefficient `c₂/σ`.
    (h1d2 : ∀ (F : ℝ → ℝ) (t₀ α β u v : ℝ), α ≤ u → u ≤ v → v ≤ β →
      (∀ t ∈ Set.Icc α β, 0 ≤ F t) → LogConcaveOn (Set.Icc α β) F →
      IntervalIntegrable (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β →
      c₂ / σ * (v - u) *
            ((∫ t in α..u, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
              (∫ t in v..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))))
        ≤ (∫ t in α..β, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) *
            (∫ t in u..v, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)))) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have hgauss : IsLogConcave
      (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) :=
    isLogConcave_gaussian σ
  have h0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  have hhc : IsLogConcave h := by
    have he : h = fun x => f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := funext hh
    rw [he]
    exact IsLogConcave.mul hfc hgauss hf₀ fun _ => (Real.exp_pos _).le
  by_contra hcon
  push Not at hcon
  set M := ∫ x, h x with hM
  set m₁ := ∫ x in S₁, h x with hm₁def
  set m₂ := ∫ x in S₂, h x with hm₂def
  set m₃ := ∫ x in S₃, h x with hm₃def
  have hm₁ : 0 ≤ m₁ := integral_nonneg fun x => h0 x
  have hm₂ : 0 ≤ m₂ := integral_nonneg fun x => h0 x
  have hm₃ : 0 ≤ m₃ := integral_nonneg fun x => h0 x
  have hpos : 0 < d / σ * (m₁ * m₂) := lt_of_le_of_lt (mul_nonneg hmass.le hm₃) hcon
  have hdσ : 0 < d / σ := by
    rcases le_or_gt (d / σ) 0 with hle | hgt
    · exact absurd hpos (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hle (mul_nonneg hm₁ hm₂)))
    · exact hgt
  have hm₁pos : 0 < m₁ := by
    rcases eq_or_lt_of_le hm₁ with he | hlt
    · exfalso; rw [← he] at hpos; simp at hpos
    · exact hlt
  set A := m₁ / M with hA
  have hApos : 0 < A := div_pos hm₁pos hmass
  have rel1 : m₁ = A * M := (div_mul_cancel₀ m₁ hmass.ne').symm
  have rel2 : m₃ < d / σ * A * m₂ := by
    have h' : M * m₃ < M * (d / σ * A * m₂) := by
      have hrw : M * (d / σ * A * m₂) = d / σ * (m₁ * m₂) := by
        rw [hA]; field_simp
      rw [hrw]; exact hcon
    exact lt_of_mul_lt_mul_left h' hmass.le
  -- localisation, with a concave profile
  obtain ⟨p, e, l, α, β, he1, hαβ, hlnn, hlc, hint, hZ1, hZ3⟩ := hloc A hApos rel1 rel2
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := needleMap p e with hγ
  set D : ℝ → ℝ := fun t => l t ^ (n - 1) * h (γ t) with hD
  have hγc : Continuous γ := by
    rw [hγ]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t := fun t ht =>
    mul_nonneg (pow_nonneg (hlnn t ht) _) (h0 _)
  have hmZ1 : MeasurableSet (γ ⁻¹' S₁ ∩ Set.Icc α β) :=
    (hγc.measurable hS₁).inter measurableSet_Icc
  have hmZ2 : MeasurableSet (γ ⁻¹' S₂ ∩ Set.Icc α β) :=
    (hγc.measurable hS₂).inter measurableSet_Icc
  have hmZ3 : MeasurableSet (γ ⁻¹' S₃ ∩ Set.Icc α β) :=
    (hγc.measurable hS₃).inter measurableSet_Icc
  -- the induced three-way partition of the parameter interval
  have hpart' : IsPartition3 (Set.Icc α β) (γ ⁻¹' S₁ ∩ Set.Icc α β)
      (γ ⁻¹' S₂ ∩ Set.Icc α β) (γ ⁻¹' S₃ ∩ Set.Icc α β) := by
    have h1 := isPartition3_inter (T := Set.Icc α β) (hpart.preimage γ)
    rwa [Set.preimage_univ, Set.univ_inter] at h1
  -- the needle carries positive mass
  have hIccint : IntegrableOn D (Set.Icc α β) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mp hint
  have hZ3nn : 0 ≤ ∫ t in γ ⁻¹' S₃ ∩ Set.Icc α β, D t :=
    setIntegral_nonneg hmZ3 fun x hx => hD0 x hx.2
  have hZ2pos : 0 < ∫ t in γ ⁻¹' S₂ ∩ Set.Icc α β, D t := by
    rcases le_or_gt (∫ t in γ ⁻¹' S₂ ∩ Set.Icc α β, D t) 0 with hle | hgt
    · exact absurd hZ3 (not_lt.mpr (le_trans
        (mul_nonpos_of_nonneg_of_nonpos (mul_pos hdσ hApos).le hle) hZ3nn))
    · exact hgt
  have hIccle : (∫ t in γ ⁻¹' S₂ ∩ Set.Icc α β, D t) ≤ ∫ t in α..β, D t := by
    have h1 : (∫ t in γ ⁻¹' S₂ ∩ Set.Icc α β, D t) ≤ ∫ t in Set.Icc α β, D t :=
      setIntegral_mono_set hIccint
        (ae_restrict_of_forall_mem measurableSet_Icc hD0)
        (Set.inter_subset_right).eventuallyLE
    rwa [intervalIntegral.integral_of_le hαβ, ← integral_Icc_eq_integral_Ioc]
  have hIpos : 0 < ∫ t in α..β, D t := lt_of_lt_of_le hZ2pos hIccle
  -- the Gaussian factor along the needle, and the log-concave cofactor `F`
  set t₀ : ℝ := -(inner ℝ p e) with ht₀
  set K : ℝ := Real.exp (-(‖p‖ ^ 2 - (inner ℝ p e) ^ 2) / (2 * σ ^ 2)) with hK
  set F : ℝ → ℝ := fun t => K * (l t ^ (n - 1) * f (γ t)) with hF
  have hFD : ∀ t, F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2)) = D t := by
    intro t
    have hg := gaussian_needleMap p e he1 hσ t
    rw [← hγ, ← hK, ← ht₀] at hg
    simp only [hF, hD, hh (γ t), hg]
    ring
  have hF0 : ∀ t ∈ Set.Icc α β, 0 ≤ F t := fun t ht =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (pow_nonneg (hlnn t ht) _) (hf₀ _))
  have hFc : LogConcaveOn (Set.Icc α β) F := by
    refine LogConcaveOn.const_mul ?_ ?_ (Real.exp_pos _).le
    · exact LogConcaveOn.mul
        (logConcaveOn_pow_of_concaveOn hlc (fun _ ht => hlnn _ ht) (n - 1))
        ((hfc.comp_needleMap p e).logConcaveOn (convex_Icc α β))
        (fun t ht => pow_nonneg (hlnn t ht) _) (fun _ _ => hf₀ _)
    · exact fun t ht => mul_nonneg (pow_nonneg (hlnn t ht) _) (hf₀ _)
  have hintF : IntervalIntegrable
      (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β := by
    simpa only [hFD] using hint
  have hg0 : ∀ t ∈ Set.Icc α β, 0 ≤ h (γ t) := fun t _ => h0 _
  have hgc : LogConcaveOn (Set.Icc α β) (fun t => h (γ t)) :=
    (hhc.comp_needleMap p e).logConcaveOn (convex_Icc α β)
  -- the coefficient function the needle carries, and its two properties
  set κ : ℝ → ℝ → ℝ := fun x y =>
    max (densDist (fun t => h (γ t)) x y / (4 * Real.sqrt n))
      (c₂ / σ * (y - x)) with hκ
  have hκ1 : ∀ x y : ℝ, α ≤ x → x ≤ y → y ≤ β →
      κ x y * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
        ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t := by
    intro x y hx hxy hy
    have hone := kls38_concave hn hx hxy hy hg0 hgc hlnn hlc hint
    have htwo := h1d2 F t₀ α β x y hx hxy hy hF0 hFc hintF
    simp only [hFD] at htwo
    exact oneDimCoeff_mul_le' hn hone htwo
  have hdd : ∀ s t : ℝ, densDist (fun u => h (γ u)) (min s t) (max s t)
      = densDist h (γ s) (γ t) := by
    intro s t
    rcases le_total s t with hst | hst
    · rw [min_eq_left hst, max_eq_right hst]; rfl
    · rw [min_eq_right hst, max_eq_left hst]
      exact densDist_comm _ _ _
  have hκ2 : ∀ s ∈ γ ⁻¹' S₁ ∩ Set.Icc α β, ∀ t ∈ γ ⁻¹' S₂ ∩ Set.Icc α β,
      d / σ ≤ κ (min s t) (max s t) := by
    intro s hs t ht
    have hnorm : ‖γ s - γ t‖ = max s t - min s t := by
      have hdst := dist_needleMap p e s t
      rw [dist_eq_norm, Real.dist_eq, he1, mul_one] at hdst
      rw [hγ, hdst, ← max_sub_min_eq_abs, max_comm t s, min_comm t s]
    have hsep' := hsep (γ s) hs.1 (γ t) ht.1
    rw [hnorm] at hsep'
    rw [hκ]
    simp only
    rw [hdd s t]
    exact le_oneDimCoeff_of_sep' hn hσ hc₂ hsep'
  -- the one-dimensional isoperimetric inequality for the induced partition
  have hiso := oneDim_partition D _ _ _ κ α β (d / σ) hαβ hD0 hint hpart' hmZ1 hmZ2 hmZ3 hκ1 hκ2
  exact needle_masses_contradiction hIpos hZ1 hZ3 hiso

end MainGeneric

/-! ### The theorem: `hloc` is the only residual binder -/

section Main

variable {n : ℕ}

/-- **Cousins–Vempala, Theorem 3.4 (`thm:iso`, `vol3_journal.tex:467`), with the Localization
Lemma as its only residual hypothesis.**

Let `π` be `N(0, σ²Iₙ)` restricted by a log-concave `f : ℝⁿ → ℝ₊`, i.e. `π` has density
proportional to `h(x) = f(x)·exp(−‖x‖²/2σ²)`.  Let `S₁, S₂, S₃` partition `ℝⁿ` so that for every
`u ∈ S₁` and `v ∈ S₂`,

* either `‖u − v‖ ≥ 2√3·d`,
* or `d_h(u,v) ≥ 4(d/σ)√n`.

Then `π(S₃) ≥ (d/σ)·π(S₁)·π(S₂)`, here in the division-free form
`(d/σ)·(∫_{S₁} h)(∫_{S₂} h) ≤ (∫ h)(∫_{S₃} h)`.

This is `Arlib.gaussianRestricted_isoperimetry` with three of its four external inputs
discharged — `hcombinatorial` by `Arlib.oneDim_partition`, `(1d-1)` by `Arlib.kls38_concave`,
`(1d-2)` by `Arlib.oneDim_isoperimetry_gaussianFactor_unconditional` — leaving **`hloc`**, the
Localization Lemma, as the only binder.

**The cost of discharging `(1d-2)`, quoted here with the result.**  The paper's metric threshold
is `d / ln 2 ≈ 1.443·d`, coming from its `(1d-2)` coefficient `\iso = ln 2`.  What this
repository proves is `(1d-2)` at `1/(2√3) ≈ 0.2887`, so the threshold above is `2√3·d ≈ 3.464·d`
— larger by the constant factor `2√3·ln 2 ≈ 2.401`.  The conclusion is unchanged (still the
sharp `d/σ`), and the density branch is unchanged; only the metric branch demands more
separation.  See the module docstring.

**`hloc` is stated for a concave profile**, `l ≥ 0` with `ConcaveOn ℝ (Set.Icc α β) l` and
needle density `l^{n−1}·h∘γ` — which is what this repository's localization stack delivers, and
what `Arlib.exists_convex_slice_profile_not_affine` shows cannot be upgraded to affine.

**Discrepancy with the printed statement.**  The paper prints the density branch as
`d_h(u,v) ≥ 4d√n`, with no `σ`; that is correct only at `σ = 1`.  See the docstring of
`Arlib.gaussianRestricted_isoperimetry` for the rescaling argument and for why the paper's own
downstream use at `vol3_journal.tex:647` survives the correction. -/
theorem gaussianRestricted_isoperimetry_concave (hn : 0 < n) {σ d : ℝ} (hσ : 0 < σ)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v)
    -- **(L)** The Localization Lemma of Lovász–Simonovits (KLS 1995, Corollary 2.4), applied to
    -- `g₁ = 1_{S₁}h − A·h` and `g₂ = (d/σ)A·1_{S₂}h − 1_{S₃}h`; `vol3_journal.tex:479–493`.
    -- Arclength-parameterised (`‖e‖ = 1`), with a **concave** profile `l`: that is the form
    -- `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear` delivers.  This is the only
    -- hypothesis of this theorem that is not geometry or analysis of the data.
    (hloc : ∀ A : ℝ, 0 < A →
      (∫ x in S₁, h x) = A * ∫ x, h x →
      (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (l : ℝ → ℝ) (α β : ℝ),
        ‖e‖ = 1 ∧ α ≤ β ∧ (∀ t ∈ Set.Icc α β, 0 ≤ l t) ∧
        ConcaveOn ℝ (Set.Icc α β) l ∧
        IntervalIntegrable
          (fun t => l t ^ (n - 1) * h (needleMap p e t)) volume α β ∧
        (∫ t in needleMap p e ⁻¹' S₁ ∩ Set.Icc α β,
            l t ^ (n - 1) * h (needleMap p e t))
          = A * ∫ t in α..β, l t ^ (n - 1) * h (needleMap p e t) ∧
        (∫ t in needleMap p e ⁻¹' S₃ ∩ Set.Icc α β,
            l t ^ (n - 1) * h (needleMap p e t))
          < d / σ * A * ∫ t in needleMap p e ⁻¹' S₂ ∩ Set.Icc α β,
              l t ^ (n - 1) * h (needleMap p e t)) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine gaussianRestricted_isoperimetry_concave_of_oneDim hn hσ (by positivity) hf₀ hfc hh
    hpart hS₁ hS₂ hS₃ hmass ?_ hloc
    (fun F t₀ α β u v hau huv hvβ hF0 hFc hint =>
      oneDim_isoperimetry_gaussianFactor_unconditional hσ F t₀ α β u v hau huv hvβ hF0 hFc hint)
  intro u hu v hv
  rcases hsep u hu v hv with hmetric | hdens
  · left
    have hrw : d / (1 / (2 * Real.sqrt 3)) = 2 * Real.sqrt 3 * d := by
      rw [div_div_eq_mul_div, div_one]; ring
    rw [hrw]
    exact hmetric
  · exact Or.inr hdens

end Main

/-! ### Non-vacuity: every hypothesis holds together, `hloc` included -/

section Witness

variable {n : ℕ}

/-- **Non-vacuity witness for `Arlib.gaussianRestricted_isoperimetry_concave`.**

Every hypothesis of the theorem — including the residual `hloc` — is satisfiable
simultaneously, at parameters where its conclusion is a *strictly positive* lower bound (so the
statement is not the trivial `0 ≤ something`).  The instance is `σ = 1`, `f` the indicator of
the unit ball (log-concave, so `h` is the Gaussian restricted to that ball), and `S₁, S₂, S₃`
the slab partition of width `1/2` orthogonal to the first coordinate axis, exactly as in
`Arlib.gaussianRestricted_isoperimetry_witness`.

The one new ingredient is `d`.  It is taken to be

  `d = min (1/8) ((∫h)·(∫_{S₃}h) / ((∫_{S₁}h)·(∫_{S₂}h)))`,

which is positive because all four integrals are.  The first term keeps the metric branch of the
separation hypothesis firing (`2√3·d ≤ 2·2·(1/8) = 1/2 ≤ ‖u − v‖`, using `√3 ≤ 2`); the second
makes `hloc`'s antecedent *provably contradictory* — `(∫_{S₁}h) = A(∫h)` and
`(∫_{S₃}h) < dA(∫_{S₂}h)` give `(∫h)(∫_{S₃}h) < d(∫_{S₁}h)(∫_{S₂}h) ≤ (∫h)(∫_{S₃}h)` — so `hloc`
holds here, vacuously but verifiably.  That is strictly more than
`Arlib.gaussianRestricted_isoperimetry_witness` shows, which leaves `hloc` out of the witness
altogether. -/
theorem gaussianRestricted_isoperimetry_concave_witness (hn : 0 < n) :
    ∃ (f h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d : ℝ),
      0 < σ ∧ 0 < d ∧ (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧
      (∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (0 < ∫ x, h x) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) ∧
      (∀ A : ℝ, 0 < A →
        (∫ x in S₁, h x) = A * ∫ x, h x →
        (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
        ∃ (p e : EuclideanSpace ℝ (Fin n)) (l : ℝ → ℝ) (α β : ℝ),
          ‖e‖ = 1 ∧ α ≤ β ∧ (∀ t ∈ Set.Icc α β, 0 ≤ l t) ∧
          ConcaveOn ℝ (Set.Icc α β) l ∧
          IntervalIntegrable
            (fun t => l t ^ (n - 1) * h (needleMap p e t)) volume α β ∧
          (∫ t in needleMap p e ⁻¹' S₁ ∩ Set.Icc α β,
              l t ^ (n - 1) * h (needleMap p e t))
            = A * ∫ t in α..β, l t ^ (n - 1) * h (needleMap p e t) ∧
          (∫ t in needleMap p e ⁻¹' S₃ ∩ Set.Icc α β,
              l t ^ (n - 1) * h (needleMap p e t))
            < d / σ * A * ∫ t in needleMap p e ⁻¹' S₂ ∩ Set.Icc α β,
                l t ^ (n - 1) * h (needleMap p e t)) ∧
      0 < d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) := by
  classical
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1 with hB
  set f : EuclideanSpace ℝ (Fin n) → ℝ := Set.indicator B 1 with hfdef
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => f x * Real.exp (-‖x‖ ^ 2 / (2 * (1:ℝ) ^ 2)) with hhdef
  have hf0 : ∀ x, 0 ≤ f x := fun x =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hfc : IsLogConcave f := isLogConcave_indicator_iff.mpr (convex_closedBall 0 1)
  have h0 : ∀ x, 0 ≤ h x := fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le
  -- `h` is the Gaussian restricted to the unit ball, hence integrable
  have hheq : h = Set.indicator B (fun x => Real.exp (-‖x‖ ^ 2 / (2 * (1:ℝ) ^ 2))) := by
    funext x
    by_cases hx : x ∈ B
    · simp [hhdef, hfdef, Set.indicator_of_mem hx]
    · simp [hhdef, hfdef, Set.indicator_of_notMem hx]
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x‖ ^ 2 / (2 * (1:ℝ) ^ 2)) := by fun_prop
  have hintg : Integrable h := by
    rw [hheq]
    refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
    exact hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
  -- balls of radius `1/8` about `r·e`, for `|r| ≤ 1/2`, sit in the unit ball
  have hballs : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1/8),
      ‖x‖ ≤ 1 ∧ |(inner ℝ e x : ℝ) - r| < 1/8 := by
    intro r hr x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hre : ‖r • e‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, he, mul_one]; exact hr
    refine ⟨?_, ?_⟩
    · have hle : ‖x‖ ≤ ‖x - r • e‖ + ‖r • e‖ := by
        simpa using norm_add_le (x - r • e) (r • e)
      linarith
    · have hip := abs_real_inner_le_norm e (x - r • e)
      rw [he, one_mul, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, he] at hip
      simpa using hip.trans_lt hx
  have hlow : ∀ r : ℝ, |r| ≤ 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1/8),
      Real.exp (-(1:ℝ)/2) ≤ h x := by
    intro r hr x hx
    obtain ⟨hx1, -⟩ := hballs r hr x hx
    have hxB : x ∈ B := by rw [hB]; simpa [Metric.mem_closedBall] using hx1
    simp only [hhdef, hfdef, Set.indicator_of_mem hxB, Pi.one_apply, one_mul]
    refine Real.exp_le_exp.mpr ?_
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have h2 : (2:ℝ) * 1 ^ 2 = 2 := by norm_num
    rw [h2]
    linarith
  have hme : Measurable fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) :=
    (continuous_const.inner continuous_id).measurable
  set S₁ : Set (EuclideanSpace ℝ (Fin n)) := {x | inner ℝ e x < -(1/4 : ℝ)} with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin n)) := {x | (1/4 : ℝ) < inner ℝ e x} with hS₂def
  set S₃ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | -(1/4 : ℝ) ≤ inner ℝ e x ∧ (inner ℝ e x : ℝ) ≤ 1/4} with hS₃def
  -- all four masses are positive
  have hM : 0 < ∫ x, h x := by
    have hpos := setIntegral_pos_of_ball_le (z := ((1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hintg h0 (by norm_num) (Real.exp_pos _) (Set.subset_univ _)
      (hlow (1/2) (by norm_num))
    rwa [setIntegral_univ] at hpos
  have hp1 : 0 < ∫ x in S₁, h x := by
    refine setIntegral_pos_of_ball_le (z := (-(1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hintg h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (-(1/2)) (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (-(1/2)) (by norm_num) x hx
    rw [hS₁def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.2]
  have hp2 : 0 < ∫ x in S₂, h x := by
    refine setIntegral_pos_of_ball_le (z := ((1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hintg h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow (1/2) (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs (1/2) (by norm_num) x hx
    rw [hS₂def]
    simp only [Set.mem_setOf_eq]
    rw [abs_lt] at hx2
    linarith [hx2.1]
  have hp3 : 0 < ∫ x in S₃, h x := by
    refine setIntegral_pos_of_ball_le (z := ((0 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hintg h0 (by norm_num) (Real.exp_pos _) ?_
      (hlow 0 (by norm_num))
    intro x hx
    obtain ⟨-, hx2⟩ := hballs 0 (by norm_num) x hx
    rw [hS₃def]
    simp only [Set.mem_setOf_eq]
    rw [sub_zero, abs_lt] at hx2
    exact ⟨by linarith [hx2.1], by linarith [hx2.2]⟩
  -- the separation parameter
  set d : ℝ := min (1/8)
    ((∫ x, h x) * (∫ x in S₃, h x) / ((∫ x in S₁, h x) * ∫ x in S₂, h x)) with hddef
  have hd0 : 0 < d :=
    lt_min (by norm_num) (div_pos (mul_pos hM hp3) (mul_pos hp1 hp2))
  have hd8 : d ≤ 1/8 := min_le_left _ _
  have hdle : d * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
    have hden : 0 < (∫ x in S₁, h x) * ∫ x in S₂, h x := mul_pos hp1 hp2
    have hmin : d ≤ (∫ x, h x) * (∫ x in S₃, h x) / ((∫ x in S₁, h x) * ∫ x in S₂, h x) :=
      min_le_right _ _
    calc d * ((∫ x in S₁, h x) * ∫ x in S₂, h x)
        ≤ ((∫ x, h x) * (∫ x in S₃, h x) / ((∫ x in S₁, h x) * ∫ x in S₂, h x))
            * ((∫ x in S₁, h x) * ∫ x in S₂, h x) :=
          mul_le_mul_of_nonneg_right hmin hden.le
      _ = (∫ x, h x) * ∫ x in S₃, h x := div_mul_cancel₀ _ hden.ne'
  refine ⟨f, h, S₁, S₂, S₃, 1, d, one_pos, hd0, hf0, hfc, fun x => by simp only [hhdef],
    isPartition3_slab e (by norm_num : (0:ℝ) ≤ 1/4), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact measurableSet_lt hme measurable_const
  · exact measurableSet_lt measurable_const hme
  · exact (measurableSet_le measurable_const hme).inter (measurableSet_le hme measurable_const)
  · exact hM
  · -- separation: the metric branch, `2√3·d ≤ 2·2·(1/8) = 1/2 ≤ ‖u − v‖`
    intro u hu v hv
    left
    have hgeo := two_mul_le_norm_sub_of_inner_lt (e := e) he (c := (1/4 : ℝ)) hu hv
    have hs3 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs3) hd0.le]
  · -- `hloc` holds vacuously: its antecedent is contradictory at this `d`
    intro A hApos hrel1 hrel2
    exfalso
    have hstep : (∫ x, h x) * (∫ x in S₃, h x)
        < (∫ x, h x) * (d / 1 * A * ∫ x in S₂, h x) :=
      mul_lt_mul_of_pos_left hrel2 hM
    have hrw : (∫ x, h x) * (d / 1 * A * ∫ x in S₂, h x)
        = d * ((∫ x in S₁, h x) * ∫ x in S₂, h x) := by
      rw [hrel1]; ring
    rw [hrw] at hstep
    linarith
  · -- the left-hand side is strictly positive
    have hd1 : (0:ℝ) < d / 1 := by rw [div_one]; exact hd0
    exact mul_pos hd1 (mul_pos hp1 hp2)

end Witness

end Arlib

/-! ### Axiom audit

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Arlib.oneDimCoeff_mul_le'
#print axioms Arlib.le_oneDimCoeff_of_sep'
#print axioms Arlib.gaussianRestricted_isoperimetry_concave_of_oneDim
#print axioms Arlib.gaussianRestricted_isoperimetry_concave
#print axioms Arlib.gaussianRestricted_isoperimetry_concave_witness
