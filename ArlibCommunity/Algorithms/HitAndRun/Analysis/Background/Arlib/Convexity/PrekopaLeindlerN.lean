/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.PrekopaLeindler
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The Prékopa–Leindler inequality in `ℝⁿ`, and Brunn–Minkowski

The headline results are

* `Arlib.prekopa_leindler_pi` — for `lam ∈ (0,1)` and measurable, nonnegative, integrable
  `f g h : (Fin n → ℝ) → ℝ` with `f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)`
  for all `x y`, one has `(∫ f) ^ lam * (∫ g) ^ (1 - lam) ≤ ∫ h` (`^` is `Real.rpow`);
* `Arlib.brunn_minkowski_pi` — the multiplicative Brunn–Minkowski inequality
  `volume A ^ lam * volume B ^ (1 - lam) ≤ volume (lam • A + (1 - lam) • B)`.

Mathlib (v4.32) has neither, in any dimension; the one-dimensional case is proved in
`Arlib.Convexity.PrekopaLeindler`, and this file runs the induction on the dimension.

## The `ℝ≥0∞` formulation

The induction is carried out for the statement `Arlib.PrekopaLeindlerLIntegral μ`, which is the
Prékopa–Leindler inequality for *lower Lebesgue* integrals of `ℝ≥0∞`-valued functions.  This is
not cosmetic: it carries **no integrability hypotheses**, so

* Tonelli's theorem applies to the product-measure step with no side conditions, and
* no junk values appear — in the Bochner formulation the slices `x ↦ h (x, u)` are integrable
  only for *almost every* `u`, while the induction needs the sliced inequality for *every* `u`.

The chain of results is:

* `prekopaLeindlerLIntegral_of_subsingleton` — the zero-dimensional base case.
* `PrekopaLeindlerLIntegral.prod` — the inductive step: the inequality for `μ` and for `ν`
  gives the inequality for `μ.prod ν` (slice, apply the inequality on the first factor to the
  slices, apply the inequality on the second factor to the marginals, Tonelli).
* `PrekopaLeindlerLIntegral.of_measurableEquiv` — transport along a measure-preserving
  measurable equivalence whose inverse respects linear combinations.
* `plCutoff` and the lemmas around it, then `prekopa_leindler_one_dim_lintegral` — the
  one-dimensional `ℝ≥0∞` statement, obtained from `Arlib.prekopa_leindler_one_dim` by cutting
  off at height `n` outside `[-n, n]` (which preserves the Prékopa–Leindler hypothesis, since
  `[-n, n]` is convex and `n ^ lam * n ^ (1 - lam) = n`) and letting `n → ∞` by monotone
  convergence.  The supremum is moved through `x ↦ x ^ lam` by `iSup_rpow_of_pos`.
* `prekopa_leindler_lintegral_pi` — the induction on `n`, splitting
  `ℝⁿ⁺¹ = ℝ × ℝⁿ` with `MeasurableEquiv.piFinSuccAbove`.
* `prekopa_leindler_pi` and `brunn_minkowski_pi` — the consequences stated above.
-/

open MeasureTheory Set Pointwise
open scoped ENNReal

namespace Arlib

/-- The **Prékopa–Leindler inequality for the measure `μ`**, in `ℝ≥0∞` (lower Lebesgue integral)
form.  This is a `Prop`-valued *abbreviation for a statement*, not an assertion: it is the
statement that will be proved, by induction on the dimension, for Lebesgue measure on
`Fin n → ℝ`.

Explicitly, `PrekopaLeindlerLIntegral μ` says: for every `lam ∈ (0,1)` and all measurable
`f g h : E → ℝ≥0∞` with `f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)` for all
`x y`, one has `(∫⁻ f) ^ lam * (∫⁻ g) ^ (1 - lam) ≤ ∫⁻ h`, where `^` is `ENNReal.rpow`.

The `ℝ≥0∞` formulation is used for the induction because it needs no integrability hypotheses
at all, so Tonelli's theorem applies without side conditions and no junk values arise from
non-integrable slices.  The Bochner-integral statement is recovered at the very end in
`prekopa_leindler_pi`. -/
def PrekopaLeindlerLIntegral {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) : Prop :=
  ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (f g h : E → ℝ≥0∞), Measurable f → Measurable g →
    Measurable h → (∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)) →
    (∫⁻ x, f x ∂μ) ^ lam * (∫⁻ x, g x ∂μ) ^ (1 - lam) ≤ ∫⁻ x, h x ∂μ

/-- **Base case of the dimension induction.**  On a subsingleton (in particular on
`Fin 0 → ℝ`, the zero-dimensional space) the Prékopa–Leindler inequality holds for *every*
measure: all three integrals are the value at `0` times the total mass, and
`m ^ lam * m ^ (1 - lam) = m`. -/
theorem prekopaLeindlerLIntegral_of_subsingleton {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [Module ℝ E] [Subsingleton E] (μ : Measure E) : PrekopaLeindlerLIntegral μ := by
  intro lam hlam0 hlam1 f g h _ _ _ hyp
  have hlam1' : (0 : ℝ) ≤ 1 - lam := by linarith
  have hconst : ∀ F : E → ℝ≥0∞, ∫⁻ x, F x ∂μ = F 0 * μ univ := by
    intro F
    calc ∫⁻ x, F x ∂μ = ∫⁻ _ : E, F 0 ∂μ :=
          lintegral_congr fun x => by rw [Subsingleton.elim x 0]
      _ = F 0 * μ univ := lintegral_const _
  have hkey : f 0 ^ lam * g 0 ^ (1 - lam) ≤ h 0 := by
    have := hyp 0 0
    simpa using this
  set m : ℝ≥0∞ := μ univ with hm
  calc (∫⁻ x, f x ∂μ) ^ lam * (∫⁻ x, g x ∂μ) ^ (1 - lam)
      = (f 0 * m) ^ lam * (g 0 * m) ^ (1 - lam) := by rw [hconst f, hconst g]
    _ = (f 0 ^ lam * g 0 ^ (1 - lam)) * (m ^ lam * m ^ (1 - lam)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hlam0.le, ENNReal.mul_rpow_of_nonneg _ _ hlam1']
        ring
    _ = (f 0 ^ lam * g 0 ^ (1 - lam)) * m := by
        rw [← ENNReal.rpow_add_of_nonneg lam (1 - lam) hlam0.le hlam1']
        norm_num
    _ ≤ h 0 * m := by gcongr
    _ = ∫⁻ x, h x ∂μ := (hconst h).symm

/-- **The inductive step, in product form.**  If the Prékopa–Leindler inequality holds for `μ`
on `α` and for `ν` on `β`, then it holds for the product measure on `α × β`.

The proof is the classical one: fix the second coordinates `s, t` and apply the inequality on
`α` to the slices `x ↦ f (x, s)`, `y ↦ g (y, t)` and `z ↦ h (z, lam • s + (1 - lam) • t)`.
This says exactly that the three *marginal* functions `s ↦ ∫⁻ x, f (x, s) ∂μ` etc. satisfy the
Prékopa–Leindler hypothesis on `β`, so the inequality on `β` applies to them; Tonelli's theorem
then rewrites the iterated integrals as integrals over `α × β`.

Because the statement is phrased with lower Lebesgue integrals there are **no** integrability
side conditions: this is precisely why `PrekopaLeindlerLIntegral` is formulated in `ℝ≥0∞`. -/
theorem PrekopaLeindlerLIntegral.prod {α β : Type*} [MeasurableSpace α] [AddCommGroup α]
    [Module ℝ α] [MeasurableSpace β] [AddCommGroup β] [Module ℝ β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (hμ : PrekopaLeindlerLIntegral μ) (hν : PrekopaLeindlerLIntegral ν) :
    PrekopaLeindlerLIntegral (μ.prod ν) := by
  intro lam hlam0 hlam1 f g h hfm hgm hhm hyp
  have hslice : ∀ (F : α × β → ℝ≥0∞), Measurable F → ∀ s : β, Measurable fun x => F (x, s) :=
    fun F hFm s => hFm.comp (measurable_id.prodMk measurable_const)
  have hyp' : ∀ s t : β,
      (∫⁻ x, f (x, s) ∂μ) ^ lam * (∫⁻ x, g (x, t) ∂μ) ^ (1 - lam)
        ≤ ∫⁻ x, h (x, lam • s + (1 - lam) • t) ∂μ := by
    intro s t
    refine hμ lam hlam0 hlam1 _ _ _ (hslice f hfm s) (hslice g hgm t)
      (hslice h hhm (lam • s + (1 - lam) • t)) ?_
    intro x y
    have := hyp (x, s) (y, t)
    simpa [Prod.smul_mk, Prod.mk_add_mk] using this
  rw [lintegral_prod_symm' _ hfm, lintegral_prod_symm' _ hgm, lintegral_prod_symm' _ hhm]
  exact hν lam hlam0 hlam1 _ _ _ hfm.lintegral_prod_left' hgm.lintegral_prod_left'
    hhm.lintegral_prod_left' hyp'

/-- **Transport along a measure-preserving linear measurable equivalence.**  If `e : E ≃ᵐ F` is
measure preserving from `μ` to `ν` and `e.symm` respects linear combinations, then the
Prékopa–Leindler inequality for `ν` implies the one for `μ`.

Only the linearity of `e.symm` on the *two-term* combinations `a • x + b • y` is required, which
is exactly the shape appearing in the Prékopa–Leindler hypothesis. -/
theorem PrekopaLeindlerLIntegral.of_measurableEquiv {E F : Type*} [MeasurableSpace E]
    [AddCommGroup E] [Module ℝ E] [MeasurableSpace F] [AddCommGroup F] [Module ℝ F]
    {μ : Measure E} {ν : Measure F} (e : E ≃ᵐ F) (hmp : MeasurePreserving e μ ν)
    (hlin : ∀ (a b : ℝ) (x y : F), e.symm (a • x + b • y) = a • e.symm x + b • e.symm y)
    (hν : PrekopaLeindlerLIntegral ν) : PrekopaLeindlerLIntegral μ := by
  intro lam hlam0 hlam1 f g h hfm hgm hhm hyp
  have hcomp : ∀ F' : E → ℝ≥0∞, ∫⁻ y, F' (e.symm y) ∂ν = ∫⁻ x, F' x ∂μ := by
    intro F'
    rw [MeasurePreserving.lintegral_map_equiv (fun y => F' (e.symm y)) e hmp]
    simp
  rw [← hcomp f, ← hcomp g, ← hcomp h]
  refine hν lam hlam0 hlam1 _ _ _ (hfm.comp e.symm.measurable) (hgm.comp e.symm.measurable)
    (hhm.comp e.symm.measurable) ?_
  intro u v
  rw [hlin lam (1 - lam) u v]
  exact hyp (e.symm u) (e.symm v)

section Cutoff

/-- For a positive exponent, `x ↦ x ^ p` commutes with suprema on `ℝ≥0∞`: it is an order
isomorphism, with inverse `x ↦ x ^ p⁻¹`.  Mathlib has the monotonicity but not this. -/
theorem iSup_rpow_of_pos {ι : Sort*} {a : ι → ℝ≥0∞} {p : ℝ} (hp : 0 < p) :
    (⨆ i, a i) ^ p = ⨆ i, a i ^ p := by
  refine le_antisymm ?_ (iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup a i) hp.le)
  have h1 : (⨆ i, a i) ≤ (⨆ i, a i ^ p) ^ p⁻¹ := by
    refine iSup_le fun i => (ENNReal.rpow_le_rpow_iff hp).1 ?_
    rw [ENNReal.rpow_inv_rpow hp.ne']
    exact le_iSup (fun i => a i ^ p) i
  calc (⨆ i, a i) ^ p ≤ ((⨆ i, a i ^ p) ^ p⁻¹) ^ p := ENNReal.rpow_le_rpow h1 hp.le
    _ = ⨆ i, a i ^ p := ENNReal.rpow_inv_rpow hp.ne' _

/-- The truncation used to reduce the `ℝ≥0∞`-valued Prékopa–Leindler inequality on `ℝ` to the
real-valued, integrable case treated by `Arlib.prekopa_leindler_one_dim`: cut `F` off at height
`n` and set it to zero outside `[-n, n]`, then take `ENNReal.toReal`.

This is a plain definition (a truncation operator); all of its properties are proved below. -/
noncomputable def plCutoff (n : ℕ) (F : ℝ → ℝ≥0∞) : ℝ → ℝ :=
  Set.indicator (Set.Icc (-(n : ℝ)) (n : ℝ)) fun x => (min (F x) (n : ℝ≥0∞)).toReal

/-- `plCutoff` is nonnegative. -/
theorem plCutoff_nonneg (n : ℕ) (F : ℝ → ℝ≥0∞) (x : ℝ) : 0 ≤ plCutoff n F x :=
  Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x

/-- `plCutoff` is bounded above by `n`. -/
theorem plCutoff_le (n : ℕ) (F : ℝ → ℝ≥0∞) (x : ℝ) : plCutoff n F x ≤ (n : ℝ) := by
  refine Set.indicator_apply_le' (fun _ => ?_) (fun _ => Nat.cast_nonneg n)
  simpa using ENNReal.toReal_mono (by simp) (min_le_right (F x) (n : ℝ≥0∞))

/-- `plCutoff` is measurable. -/
theorem measurable_plCutoff (n : ℕ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (plCutoff n F) :=
  Measurable.indicator ((hF.min measurable_const).ennreal_toReal) measurableSet_Icc

/-- `plCutoff` is integrable: it is bounded by `n` and supported in `[-n, n]`. -/
theorem integrable_plCutoff (n : ℕ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Integrable (plCutoff n F) := by
  rw [plCutoff, integrable_indicator_iff measurableSet_Icc]
  refine Integrable.mono' (g := fun _ : ℝ => (n : ℝ)) (integrableOn_const (by simp))
    ((hF.min measurable_const).ennreal_toReal).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  simpa using ENNReal.toReal_mono (by simp) (min_le_right (F x) (n : ℝ≥0∞))

/-- `ENNReal.ofReal ∘ plCutoff n F` is the plain `ℝ≥0∞`-valued truncation: the `toReal`
round-trip is lossless because the truncated value is finite. -/
theorem ofReal_plCutoff (n : ℕ) (F : ℝ → ℝ≥0∞) (x : ℝ) :
    ENNReal.ofReal (plCutoff n F x)
      = Set.indicator (Set.Icc (-(n : ℝ)) (n : ℝ)) (fun x => min (F x) (n : ℝ≥0∞)) x := by
  by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
  · rw [plCutoff, Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) (min_le_right (F x) (n : ℝ≥0∞)))]
  · rw [plCutoff, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

/-- Cutting off at height `n` exhausts an `ℝ≥0∞`-valued function. -/
theorem iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  have : ⨆ n : ℕ, a ⊓ (n : ℝ≥0∞) = a ⊓ ⨆ n : ℕ, (n : ℝ≥0∞) := (inf_iSup_eq _ _).symm
  simpa [ENNReal.iSup_natCast] using this

/-- The truncations `plCutoff n F` increase pointwise to `F`. -/
theorem iSup_ofReal_plCutoff (F : ℝ → ℝ≥0∞) (x : ℝ) :
    ⨆ n : ℕ, ENNReal.ofReal (plCutoff n F x) = F x := by
  simp only [ofReal_plCutoff]
  refine le_antisymm
    (iSup_le fun n => Set.indicator_apply_le' (fun _ => min_le_left _ _) (fun _ => zero_le)) ?_
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  rw [← iSup_min_natCast (F x)]
  refine iSup_le fun k => ?_
  refine le_iSup_of_le (max k N) ?_
  have hx : x ∈ Set.Icc (-((max k N : ℕ) : ℝ)) ((max k N : ℕ) : ℝ) := by
    have h1 : (N : ℝ) ≤ ((max k N : ℕ) : ℝ) := Nat.cast_le.2 (le_max_right k N)
    have h2 : |x| ≤ ((max k N : ℕ) : ℝ) := hN.trans h1
    rw [abs_le] at h2
    exact ⟨h2.1, h2.2⟩
  rw [Set.indicator_of_mem hx]
  exact min_le_min le_rfl (Nat.cast_le.2 (le_max_left k N))

/-- The truncations `plCutoff n F` increase with `n`. -/
theorem monotone_ofReal_plCutoff (F : ℝ → ℝ≥0∞) :
    Monotone fun (n : ℕ) (x : ℝ) => ENNReal.ofReal (plCutoff n F x) := by
  intro m n hmn x
  simp only [ofReal_plCutoff]
  by_cases hx : x ∈ Set.Icc (-(m : ℝ)) (m : ℝ)
  · have hmn' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
    have hx' : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) := ⟨by simp at hx ⊢; linarith [hx.1],
      by simp at hx ⊢; linarith [hx.2]⟩
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    exact min_le_min le_rfl (Nat.cast_le.2 hmn)
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

/-- The lower Lebesgue integrals of the truncations increase with `n`. -/
theorem monotone_lintegral_ofReal_plCutoff (F : ℝ → ℝ≥0∞) :
    Monotone fun n : ℕ => ∫⁻ x, ENNReal.ofReal (plCutoff n F x) :=
  fun _ _ hmn => lintegral_mono fun x => monotone_ofReal_plCutoff F hmn x

/-- **Monotone convergence for the truncations.**  The lower Lebesgue integrals of the
truncations `plCutoff n F` increase to the lower Lebesgue integral of `F`. -/
theorem iSup_lintegral_ofReal_plCutoff {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (plCutoff n F x) = ∫⁻ x, F x := by
  have hmeas : ∀ n : ℕ, Measurable fun x => ENNReal.ofReal (plCutoff n F x) :=
    fun n => (measurable_plCutoff n hF).ennreal_ofReal
  rw [← lintegral_iSup hmeas (monotone_ofReal_plCutoff F)]
  exact lintegral_congr fun x => iSup_ofReal_plCutoff F x

/-- **The Prékopa–Leindler hypothesis survives truncation.**  If `f`, `g`, `h` satisfy the
Prékopa–Leindler hypothesis then so do their truncations `plCutoff n f`, `plCutoff n g`,
`plCutoff n h`.

Two facts make this work: the cut-off region `[-n, n]` is convex, so the combination
`lam * x + (1 - lam) * y` stays inside it; and the height cut is compatible with the weighted
geometric mean because `n ^ lam * n ^ (1 - lam) = n`. -/
theorem plCutoff_hyp {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) {f g h : ℝ → ℝ≥0∞}
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)) (n : ℕ) :
    ∀ x y : ℝ, plCutoff n f x ^ lam * plCutoff n g y ^ (1 - lam)
      ≤ plCutoff n h (lam * x + (1 - lam) * y) := by
  intro x y
  have hlam1' : (0 : ℝ) < 1 - lam := by linarith
  by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
  swap
  · simp only [plCutoff, Set.indicator_of_notMem hx, Real.zero_rpow hlam0.ne', zero_mul]
    exact plCutoff_nonneg _ _ _
  by_cases hy : y ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
  swap
  · simp only [plCutoff, Set.indicator_of_notMem hy, Real.zero_rpow hlam1'.ne', mul_zero]
    exact plCutoff_nonneg _ _ _
  have hz : lam * x + (1 - lam) * y ∈ Set.Icc (-(n : ℝ)) (n : ℝ) := by
    simp only [Set.mem_Icc] at hx hy ⊢
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hne : ∀ a : ℝ≥0∞, min a (n : ℝ≥0∞) ≠ ⊤ :=
    fun a => ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have key : min (f x) (n : ℝ≥0∞) ^ lam * min (g y) (n : ℝ≥0∞) ^ (1 - lam)
      ≤ min (h (lam * x + (1 - lam) * y)) (n : ℝ≥0∞) := by
    refine le_min ?_ ?_
    · refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) hlam0.le)
        (ENNReal.rpow_le_rpow (min_le_left _ _) hlam1'.le)) ?_
      simpa [smul_eq_mul] using hyp x y
    · refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_right _ _) hlam0.le)
        (ENNReal.rpow_le_rpow (min_le_right _ _) hlam1'.le)) ?_
      rw [← ENNReal.rpow_add_of_nonneg lam (1 - lam) hlam0.le hlam1'.le]
      norm_num
  simp only [plCutoff, Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (hne _) key

/-- The lower Lebesgue integral of a truncation is finite. -/
theorem lintegral_ofReal_plCutoff_ne_top (n : ℕ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, ENNReal.ofReal (plCutoff n F x)) ≠ ⊤ :=
  ((hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (plCutoff_nonneg n F))).1 (integrable_plCutoff n hF).2).ne

/-- **The Prékopa–Leindler inequality for the truncations**, in `ℝ≥0∞` form.  This is
`Arlib.prekopa_leindler_one_dim` applied to `plCutoff n f`, `plCutoff n g`, `plCutoff n h`
(which are measurable, nonnegative and integrable), transported from Bochner integrals to
lower Lebesgue integrals. -/
theorem lintegral_ofReal_plCutoff_ineq {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {f g h : ℝ → ℝ≥0∞} (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (plCutoff n f x)) ^ lam
        * (∫⁻ x, ENNReal.ofReal (plCutoff n g x)) ^ (1 - lam)
      ≤ ∫⁻ x, ENNReal.ofReal (plCutoff n h x) := by
  have hlam1' : (0 : ℝ) < 1 - lam := by linarith
  have hreal := prekopa_leindler_one_dim hlam0 hlam1
    (measurable_plCutoff n hfm) (measurable_plCutoff n hgm) (measurable_plCutoff n hhm)
    (plCutoff_nonneg n f) (plCutoff_nonneg n g)
    (integrable_plCutoff n hfm) (integrable_plCutoff n hgm) (integrable_plCutoff n hhm)
    (plCutoff_hyp hlam0 hlam1 hyp n)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (plCutoff_nonneg n f))
      (measurable_plCutoff n hfm).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (plCutoff_nonneg n g))
      (measurable_plCutoff n hgm).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (plCutoff_nonneg n h))
      (measurable_plCutoff n hhm).aestronglyMeasurable,
    ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul] at hreal
  exact (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hlam0.le (lintegral_ofReal_plCutoff_ne_top n hfm))
      (ENNReal.rpow_ne_top_of_nonneg hlam1'.le (lintegral_ofReal_plCutoff_ne_top n hgm)))
    (lintegral_ofReal_plCutoff_ne_top n hhm)).1 hreal

end Cutoff

/-- **The one-dimensional Prékopa–Leindler inequality in `ℝ≥0∞` form.**

For `lam ∈ (0,1)` and *arbitrary* measurable `f g h : ℝ → ℝ≥0∞` (no integrability, no
finiteness) with `f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)` for all `x y`,
`(∫⁻ f) ^ lam * (∫⁻ g) ^ (1 - lam) ≤ ∫⁻ h`.

This upgrades `Arlib.prekopa_leindler_one_dim` by monotone convergence along the truncations
`plCutoff n`.  It is the base case of the dimension induction. -/
theorem prekopa_leindler_one_dim_lintegral :
    PrekopaLeindlerLIntegral (volume : Measure ℝ) := by
  intro lam hlam0 hlam1 f g h hfm hgm hhm hyp
  have hlam1' : (0 : ℝ) < 1 - lam := by linarith
  rw [← iSup_lintegral_ofReal_plCutoff hfm, ← iSup_lintegral_ofReal_plCutoff hgm,
    ← iSup_lintegral_ofReal_plCutoff hhm, iSup_rpow_of_pos hlam0, iSup_rpow_of_pos hlam1',
    ENNReal.iSup_mul]
  refine iSup_le fun i => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  calc (∫⁻ x, ENNReal.ofReal (plCutoff i f x)) ^ lam
        * (∫⁻ x, ENNReal.ofReal (plCutoff j g x)) ^ (1 - lam)
      ≤ (∫⁻ x, ENNReal.ofReal (plCutoff (max i j) f x)) ^ lam
        * (∫⁻ x, ENNReal.ofReal (plCutoff (max i j) g x)) ^ (1 - lam) :=
        mul_le_mul'
          (ENNReal.rpow_le_rpow
            (monotone_lintegral_ofReal_plCutoff f (le_max_left i j)) hlam0.le)
          (ENNReal.rpow_le_rpow
            (monotone_lintegral_ofReal_plCutoff g (le_max_right i j)) hlam1'.le)
    _ ≤ ∫⁻ x, ENNReal.ofReal (plCutoff (max i j) h x) :=
        lintegral_ofReal_plCutoff_ineq hlam0 hlam1 hfm hgm hhm hyp (max i j)
    _ ≤ ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (plCutoff n h x) :=
        le_iSup (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (plCutoff n h x)) (max i j)

/-- `Fin.cons` respects linear combinations.  This is the linearity of
`(MeasurableEquiv.piFinSuccAbove _ 0).symm`, which is what
`PrekopaLeindlerLIntegral.of_measurableEquiv` consumes. -/
theorem cons_linear {n : ℕ} (a b : ℝ) (x y : ℝ × (Fin n → ℝ)) :
    (Fin.cons (a • x + b • y).1 (a • x + b • y).2 : Fin (n + 1) → ℝ)
      = a • (Fin.cons x.1 x.2 : Fin (n + 1) → ℝ)
        + b • (Fin.cons y.1 y.2 : Fin (n + 1) → ℝ) := by
  funext k
  induction k using Fin.cases with
  | zero => simp
  | succ j => simp

/-- **The Prékopa–Leindler inequality on `ℝⁿ`, in `ℝ≥0∞` form.**

For every `n`, Lebesgue measure on `Fin n → ℝ` satisfies `PrekopaLeindlerLIntegral`: for
`lam ∈ (0,1)` and measurable `f g h : (Fin n → ℝ) → ℝ≥0∞` with
`f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)` for all `x y`,
`(∫⁻ f) ^ lam * (∫⁻ g) ^ (1 - lam) ≤ ∫⁻ h`.

The proof is induction on `n`: the base case is `prekopaLeindlerLIntegral_of_subsingleton`, and
the step splits `ℝⁿ⁺¹ = ℝ × ℝⁿ` using `MeasurableEquiv.piFinSuccAbove`, combining
`prekopa_leindler_one_dim_lintegral` with the inductive hypothesis via
`PrekopaLeindlerLIntegral.prod`. -/
theorem prekopa_leindler_lintegral_pi :
    ∀ n : ℕ, PrekopaLeindlerLIntegral (volume : Measure (Fin n → ℝ))
  | 0 => by
      haveI : Subsingleton (Fin 0 → ℝ) := ⟨fun a b => funext fun i => i.elim0⟩
      exact prekopaLeindlerLIntegral_of_subsingleton _
  | (n + 1) => by
      have hprod : PrekopaLeindlerLIntegral (volume : Measure (ℝ × (Fin n → ℝ))) := by
        rw [Measure.volume_eq_prod]
        exact prekopa_leindler_one_dim_lintegral.prod (prekopa_leindler_lintegral_pi n)
      refine PrekopaLeindlerLIntegral.of_measurableEquiv
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
        (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ?_ hprod
      intro a b x y
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
      exact cons_linear a b x y

/-- Nonnegativity of `h` is automatic from the Prékopa–Leindler hypothesis on a real vector
space: take `x = y = z` and use `lam • z + (1 - lam) • z = z`. -/
theorem nonneg_of_prekopa_hyp_smul {E : Type*} [AddCommGroup E] [Module ℝ E] {lam : ℝ}
    {f g h : E → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)) (z : E) :
    0 ≤ h z := by
  have hz : lam • z + (1 - lam) • z = z := by
    rw [← add_smul]; norm_num
  have hzz := hyp z z
  rw [hz] at hzz
  exact le_trans (mul_nonneg (Real.rpow_nonneg (hf z) _) (Real.rpow_nonneg (hg z) _)) hzz

/-- **The Prékopa–Leindler inequality in `ℝⁿ`.**

Let `lam ∈ (0,1)` and let `f g h : (Fin n → ℝ) → ℝ` be measurable, nonnegative and integrable
with `f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)` for all `x y`, where `^` is
`Real.rpow`.  Then
`(∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x`.

This is the Bochner-integral form of `prekopa_leindler_lintegral_pi`; Mathlib has neither. -/
theorem prekopa_leindler_pi {n : ℕ} {lam : ℝ} {f g h : (Fin n → ℝ) → ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam • x + (1 - lam) • y)) :
    (∫ x, f x) ^ lam * (∫ x, g x) ^ (1 - lam) ≤ ∫ x, h x := by
  have hh : ∀ z, 0 ≤ h z := nonneg_of_prekopa_hyp_smul hf hg hyp
  have hlam1' : (0 : ℝ) < 1 - lam := by linarith
  have key := prekopa_leindler_lintegral_pi n lam hlam0 hlam1
    (fun x => ENNReal.ofReal (f x)) (fun x => ENNReal.ofReal (g x))
    (fun x => ENNReal.ofReal (h x))
    hfm.ennreal_ofReal hgm.ennreal_ofReal hhm.ennreal_ofReal (by
      intro x y
      rw [ENNReal.ofReal_rpow_of_nonneg (hf x) hlam0.le,
        ENNReal.ofReal_rpow_of_nonneg (hg y) hlam1'.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf x) lam)]
      exact ENNReal.ofReal_le_ofReal (hyp x y))
  have hA : (∫⁻ x, ENNReal.ofReal (f x)) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).1 hfi.2).ne
  have hB : (∫⁻ x, ENNReal.ofReal (g x)) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg)).1 hgi.2).ne
  have hC : (∫⁻ x, ENNReal.ofReal (h x)) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hh)).1 hhi.2).ne
  have hmono := ENNReal.toReal_mono hC key
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hmono
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf)
      hfm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg)
      hgm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh)
      hhm.aestronglyMeasurable]
  exact hmono

/-- **The multiplicative Brunn–Minkowski inequality in `ℝⁿ`.**

For `lam ∈ (0,1)` and measurable `A B : Set (Fin n → ℝ)`,
`volume A ^ lam * volume B ^ (1 - lam) ≤ volume (lam • A + (1 - lam) • B)`
(with `ENNReal.rpow`).

This is `prekopa_leindler_lintegral_pi` applied to the indicator functions of `A`, `B` and of
a measurable hull of `lam • A + (1 - lam) • B`.  The measurable hull is needed because a
Minkowski sum of measurable sets need not be measurable; `volume` on the right-hand side is
being used as an outer measure, exactly as in the one-dimensional
`Arlib.volume_add_volume_le_volume_add`.

Mathlib has no Brunn–Minkowski inequality in any dimension. -/
theorem brunn_minkowski_pi {n : ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {A B : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume A ^ lam * volume B ^ (1 - lam) ≤ volume (lam • A + (1 - lam) • B) := by
  have hlam1' : (0 : ℝ) < 1 - lam := by linarith
  set C : Set (Fin n → ℝ) := lam • A + (1 - lam) • B with hCdef
  set C' : Set (Fin n → ℝ) := toMeasurable volume C with hC'def
  have hC'meas : MeasurableSet C' := measurableSet_toMeasurable _ _
  have hhyp : ∀ x y : Fin n → ℝ,
      A.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) x ^ lam
          * B.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) y ^ (1 - lam)
        ≤ C'.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) (lam • x + (1 - lam) • y) := by
    intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hmem : lam • x + (1 - lam) • y ∈ C :=
          Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy)
        rw [Set.indicator_of_mem (subset_toMeasurable volume C hmem),
          Set.indicator_of_mem hx, Set.indicator_of_mem hy]
        simp
      · rw [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hlam1', mul_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hlam0, zero_mul]
      exact zero_le
  have hkey := prekopa_leindler_lintegral_pi n lam hlam0 hlam1
    (A.indicator 1) (B.indicator 1) (C'.indicator 1)
    (measurable_const.indicator hA) (measurable_const.indicator hB)
    (measurable_const.indicator hC'meas) hhyp
  rwa [lintegral_indicator_one hA, lintegral_indicator_one hB,
    lintegral_indicator_one hC'meas, measure_toMeasurable] at hkey

end Arlib
