/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Isoperimetry
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.NeedleProfile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The sharp isoperimetric inequality for Gaussian-restricted log-concave measures

This file assembles **Cousins–Vempala's Theorem 3.4** (`thm:iso`,
`1409.6011/vol3_journal.tex:467`), the sharp isoperimetric inequality that every polynomial
bound in that paper rests on:

> Let `π` be `N(0, σ²Iₙ)` restricted by a log-concave `f : ℝⁿ → ℝ₊`, i.e. `π` has density
> proportional to `h(x) = f(x)γ(x)`.  Let `S₁, S₂, S₃` partition `ℝⁿ` so that for any `u ∈ S₁`
> and `v ∈ S₂`, either `‖u − v‖ ≥ d/ln 2` or `d_h(u,v) ≥ 4d√n`.  Then
> `π(S₃) ≥ (d/σ)·π(S₁)·π(S₂)`.

(`ln 2` is the paper's `\iso` macro, `vol3_journal.tex:65`.)

## Main results

* `Arlib.needle_masses_contradiction` — the arithmetic core: for a needle of positive total
  mass `I`, the three facts `I₁ = A·I`, `I₃ < c·A·I₂` and `c·I₁·I₂ ≤ I·I₃` are contradictory.
* `Arlib.oneDimCoeff_mul_le`, `Arlib.le_oneDimCoeff_of_sep` — the `max` step: the larger of the
  two one-dimensional coefficients `d_h(x,y)/(4√n)` and `ln 2·(y−x)/σ` is itself a valid
  coefficient, and the separation hypothesis says exactly that it is at least `d/σ`.
* `Arlib.norm_needleMap_sq`, `Arlib.gaussian_needleMap` — an arclength-parameterised needle sees
  a one-dimensional Gaussian *of the same `σ`*, times a constant.  This is what makes `(1d-2)`
  statable intrinsically in one dimension.
* `Arlib.isPartition3_inter` — a three-way partition restricts to any subset.
* `Arlib.gaussianRestricted_isoperimetry` — **the theorem.**
* `Arlib.gaussianRestricted_isoperimetry_witness` — the non-vacuity witness (see below).

## The four external inputs, and who discharges them

`Arlib.gaussianRestricted_isoperimetry` has exactly four hypotheses that are not geometry or
analysis of the data.  Each is a plain binder — there is **no** `def … : Prop` packaging the
conclusion, and in particular nothing shaped like the `IsoInput`/`OneDimIso` predicate that
`Arlib.Convexity.Isoperimetry` (docstring, line 75) and
`Arlib.Convexity.Localization` (line 56) deliberately refuse to introduce.

1. **`hloc` — the Localization Lemma** of Lovász–Simonovits (KLS 1995, Corollary 2.4), applied
   to `g₁ = 1_{S₁}h − A·h` and `g₂ = (d/σ)A·1_{S₂}h − 1_{S₃}h`; `vol3_journal.tex:479–493`.
   Stated in *arclength* parameterisation `t ↦ p + t·e`, `‖e‖ = 1` (the paper writes
   `(1−t)a + tb`, `t ∈ [0,1]`; the two differ by an affine change of parameter, under which
   both displayed relations — being homogeneous of degree one in the needle measure — are
   invariant).
   *Status in this repository*: partially assembled in
   `Arlib.Convexity.LocalizationAssembly`.  `Arlib.needleIntegral_eq_zero_and_ge` delivers the
   two conclusions from the chain invariants, but its residual hypotheses **(A)** transverse
   thinness (`hδ₁`, `hδ₂`, `δ k → 0`) and **(B)/(G2c)** the affine change of coordinates are
   open there (that file's docstring, "Classification of every hypothesis").  A third mismatch
   is visible only from here: that file delivers the profile `W` merely **concave**, and
   deliberately so (`Arlib.exists_convex_slice_profile_not_affine` refutes the
   concave-to-affine upgrade), whereas `hloc` as stated here — following Cousins–Vempala —
   delivers `ℓ` *affine*.  Wiring the two together therefore needs `h1d1`/`h1d2` restated for a
   concave profile, not the affine upgrade.
2. **`hcombinatorial` — "by a standard combinatorial argument, we can assume that the `Zᵢ` are
   intervals that partition `[a,b]`"**, `vol3_journal.tex:497`.  The paper gives no proof, and
   nobody in this repository is working on it.

   It is stated here not as "the `Zᵢ` may be taken to be intervals" but as *what that sentence
   is for*: the passage from the **interval** case of the one-dimensional isoperimetric
   inequality (hypothesis `hint`, supplied by `h1d1`/`h1d2` through
   `Arlib.oneDimCoeff_mul_le`) to an arbitrary measurable three-way partition (hypothesis
   `hcross`, supplied by the separation hypothesis through
   `Arlib.le_oneDimCoeff_of_sep`).  The literal reading is **false** and would have made this
   theorem vacuous.  Concretely, with `D ≡ 1` on `[0,1]`, `A = 0.8`, `c = 4`,

   `Z₁ = [0,0.4] ∪ [0.6,1]`,  `Z₂ = (0.45,0.5)`,  `Z₃` the rest,

   both post-localisation relations hold (`∫_{Z₁} = 0.8 = A·∫`, `∫_{Z₃} = 0.15 < c·A·∫_{Z₂} =
   0.16`), yet **neither** orientation of an interval reduction exists: `∫_0^u = 0.8` forces
   `u = 0.8`, and no point of `Z₂` lies to its right; `∫_v^1 = 0.8` forces `v = 0.2`, and no
   point of `Z₂` lies to its left.  What rules that configuration out in the real argument is
   the separation between `Z₁` and `Z₂` — which the literal reading drops — and that is why
   `hcombinatorial` carries `hcross`.  In the counterexample `hcross` indeed fails: the cross
   pair `(0.4, 0.45)` forces `c ≤ κ(0.4,0.45) ≤ 0.227` through `hint`.

   As stated, `hcombinatorial` is exactly the one-dimensional isoperimetric inequality of
   Lovász–Simonovits for a general measurable partition, deduced from its interval case.
3. **`h1d1` — inequality (1d-1)**, `vol3_journal.tex:498`, cited there as Lemma 3.8 of
   Kannan–Lovász–Simonovits 1997.  **This repository does not contain it.**
   `Arlib.lem33_sqrt` / `Arlib.lintegral_volume_closedBall_sdiff_le_sqrt`
   (`Arlib/Convexity/KLS97Sharp.lean`) is *Corollary 4.6* of that paper — an `n`-dimensional
   statement `∫_K vol(B(x,t) \ K) dx ≤ …` about ball-walk step lengths — and is a different
   result from the four-integral one-dimensional inequality wanted here.  Nobody is currently
   proving `(1d-1)`.
4. **`h1d2` — inequality (1d-2)**, `vol3_journal.tex:501`, with the paper's coefficient
   `\iso = ln 2`, divided by `σ` because the needle's Gaussian factor has variance `σ²` rather
   than `1` (Brascamp–Lieb, `vol3_journal.tex:506`).  Being proved concurrently in
   `Arlib.Convexity.OneDimIsoperimetry`.  That file's target `Arlib.oneDim_isoperimetry`
   currently reaches coefficient `sup w / ∫ w ≥ 1/(2√3)` rather than `ln 2 ≈ 0.693`; if it
   lands at the weaker constant, `h1d2` here should be reinstantiated with `1/(2√3)` in place
   of `ln 2` and the separation hypothesis's first branch with `2√3·d` in place of `d/ln 2` —
   the proof below is insensitive to the value.

## Two discrepancies with the printed paper

**(i) The `σ` in the density branch.**  Cousins–Vempala print the second disjunct as
`d_h(u,v) ≥ 4d√n`, with no `σ`.  That cannot be right at general `σ`: their proof establishes
the case `σ = 1` and then rescales by `x = y/σ`, under which `‖u − v‖` scales like a length but
`d_h` is scale-*invariant* (`Arlib.densDist_const_mul` is the corresponding invariance under
renormalising `h`).  Pushing the printed hypothesis through the rescaling yields only
`π(S₃) ≥ min{d, d/σ}·π(S₁)π(S₂)`, strictly weaker than the printed `d/σ` whenever `σ < 1` —
which is the entire Gaussian-cooling regime.  The corrected disjunct is `d_h(u,v) ≥ 4(d/σ)√n`,
and it is what is proved here.

The paper's own downstream use survives the correction.  At `vol3_journal.tex:647` the theorem
is applied with `d = min{δ·ln 2/√n, 1/(16√n)}` to data satisfying "`‖u−v‖ ≥ δ/√n` or
`d_h ≥ 1/4`"; the corrected disjunct needs `4(d/σ)√n ≤ 1/4`, i.e. `d ≤ σ/(16√n)`, so the
correct choice is `d = min{δ·ln 2/√n, σ/(16√n)}`.  Since that application also has
`δ ≤ σ/(8√n)`, for every `n ≥ 2` the first term is the smaller one and `d = δ·ln 2/√n` exactly
as before; the conductance bound `Ω(δ/(σ√n))` is unchanged.

**(ii) `d_h ≤ 1` caps the density branch.**  `Arlib.densDist_le_one` shows the density branch is
*unsatisfiable* once `4d√n/σ > 1`.  This is not an error — it is why the ball-walk analysis caps
`d` at `1/(16√n)` (resp. `σ/(16√n)`) — but it means the branch carries no content at large `d`,
and any future user of this theorem must check it.

## Non-vacuity

`Arlib.gaussianRestricted_isoperimetry_witness` exhibits concrete data — `σ = 1`, `f` the
indicator of the unit ball (log-concave, so `h` is the Gaussian restricted to that ball),
`d = (ln 2)/2`, and the slab partition of width `1/2` orthogonal to the first coordinate axis —
satisfying *every* geometric hypothesis of the theorem simultaneously, with
`0 < (d/σ)·(∫_{S₁} h)(∫_{S₂} h)`.  So the conclusion is a strictly positive lower bound there,
not the trivial `0 ≤ …`, and no two geometric hypotheses are in conflict.  The four external
inputs are universally quantified statements of the literature, not properties of that
instance; at the witness `hloc`'s antecedent is unsatisfiable (its conclusion holds), so `hloc`
holds there vacuously.

## No rate claim

Nothing here says, or implies, that any algorithm runs in polynomial time.  The conductance
constants in this repository are still exponentially small
(`Arlib/MarkovChains/Continuous/MetropolisConductance.lean`;
`Arlib/Convexity/GaussianCooling/Unblock.lean:591–596`, "this is not a polynomial-time
result").  `thm:iso` is the input that would eventually change that picture — but only once
**all four** hypotheses above are discharged, and today none of them is.  Until then this file
is a conditional reduction, not a rate improvement.

## References

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian Volume*,
§3 (`1409.6011/vol3_journal.tex:404–508`).

Kannan, Lovász and Simonovits, *Isoperimetric problems for convex bodies and a localization
lemma*, Discrete Comput. Geom. **13** (1995).

Kannan, Lovász and Simonovits, *Random walks and an `O*(n⁵)` volume algorithm for convex
bodies*, Random Structures & Algorithms **11** (1997), Lemma 3.8.
-/

open MeasureTheory Set

namespace Arlib

/-! ### The arithmetic core of the contradiction -/

section Arithmetic

/-- **The contradiction that closes Cousins–Vempala's proof of `thm:iso`.**

After localisation the needle carries a total mass `I > 0` and the three partition masses
`I₁, I₂, I₃`.  The failure of the conclusion supplies `I₁ = A·I` and `I₃ < c·A·I₂`, and the
one-dimensional isoperimetric inequality supplies `c·I₁·I₂ ≤ I·I₃`.  These are jointly
contradictory: `I·I₃ < I·(c·A·I₂) = c·(A·I)·I₂ = c·I₁·I₂ ≤ I·I₃`.  No sign or nonnegativity
hypothesis on `c`, `A` or the `Iᵢ` is needed — only `0 < I`.

`vol3_journal.tex:479–495`. -/
theorem needle_masses_contradiction {I I₁ I₂ I₃ A c : ℝ} (hIpos : 0 < I) (heq : I₁ = A * I)
    (hlt : I₃ < c * A * I₂) (hiso : c * (I₁ * I₂) ≤ I * I₃) : False := by
  have hstep : I * I₃ < I * (c * A * I₂) := mul_lt_mul_of_pos_left hlt hIpos
  have hrw : I * (c * A * I₂) = c * (I₁ * I₂) := by rw [heq]; ring
  rw [hrw] at hstep
  linarith

end Arithmetic

/-! ### Combining the two one-dimensional inequalities -/

section OneDimCombination

/-- **The one-dimensional isoperimetric coefficient a needle carries.**

Cousins–Vempala's proof feeds the needle two one-dimensional inequalities — `(1d-1)` with
coefficient `d_h(x,y)/(4√n)` and `(1d-2)` with coefficient `ln 2 · (y − x) / σ` — and then uses
whichever is larger.  This lemma says the larger of the two is itself a valid coefficient.

`Dh` stands for `d_h(x,y)`, `ρ` for `y − x`, and `L`, `R`, `Mid`, `I` for the four needle masses
`∫_α^x`, `∫_y^β`, `∫_x^y`, `∫_α^β`. -/
theorem oneDimCoeff_mul_le {n : ℕ} {σ Dh ρ L R I Mid : ℝ} (hn : 0 < n) (hprod : 0 ≤ L * R)
    (h1d1 : Dh * (L * R) ≤ 4 * Real.sqrt n * (I * Mid))
    (h1d2 : Real.log 2 / σ * ρ * (L * R) ≤ I * Mid) :
    max (Dh / (4 * Real.sqrt n)) (Real.log 2 / σ * ρ) * (L * R) ≤ I * Mid := by
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsq4 : 0 < 4 * Real.sqrt n := by positivity
  rcases max_cases (Dh / (4 * Real.sqrt n)) (Real.log 2 / σ * ρ) with ⟨he, -⟩ | ⟨he, -⟩
  · rw [he, div_mul_eq_mul_div, div_le_iff₀ hsq4]
    have hcomm : I * Mid * (4 * Real.sqrt n) = 4 * Real.sqrt n * (I * Mid) := by ring
    rw [hcomm]
    exact h1d1
  · rw [he]
    exact h1d2

/-- **The separation hypothesis of `thm:iso` is exactly a lower bound on that coefficient.**

Whichever branch of the disjunction `‖u − v‖ ≥ d/ln 2` or `d_h(u,v) ≥ 4(d/σ)√n` holds, the
coefficient of `Arlib.oneDimCoeff_mul_le` is at least `d/σ`.

**Constant watch.**  The paper prints the second branch as `d_h(u,v) ≥ 4d√n`, without the `σ`.
That is correct only at `σ = 1`; see the module docstring. -/
theorem le_oneDimCoeff_of_sep {n : ℕ} {σ d ρ Dh : ℝ} (hn : 0 < n) (hσ : 0 < σ)
    (hsep : d / Real.log 2 ≤ ρ ∨ 4 * (d / σ) * Real.sqrt n ≤ Dh) :
    d / σ ≤ max (Dh / (4 * Real.sqrt n)) (Real.log 2 / σ * ρ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  rcases hsep with hmetric | hdens
  · refine le_max_of_le_right ?_
    have hrw : d / σ = Real.log 2 / σ * (d / Real.log 2) := by field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hmetric (by positivity)
  · refine le_max_of_le_left ?_
    rw [le_div_iff₀ (by positivity)]
    calc d / σ * (4 * Real.sqrt n) = 4 * (d / σ) * Real.sqrt n := by ring
      _ ≤ Dh := hdens

end OneDimCombination

/-! ### Three-way partitions restricted to a subset -/

section PartitionInter

variable {E : Type*}

/-- **A three-way partition restricts to a three-way partition of any subset.**

`Arlib.IsPartition3.preimage` carries a partition of `ℝⁿ` to a partition of the needle's whole
parameter line; this lemma then cuts it down to the needle's parameter interval. -/
theorem isPartition3_inter {K S₁ S₂ S₃ T : Set E} (h : IsPartition3 K S₁ S₂ S₃) :
    IsPartition3 (K ∩ T) (S₁ ∩ T) (S₂ ∩ T) (S₃ ∩ T) where
  union := by
    rw [← Set.union_inter_distrib_right, ← Set.union_inter_distrib_right, h.union]
  disjoint₁₂ := (h.disjoint₁₂.mono Set.inter_subset_left Set.inter_subset_left)
  disjoint₁₃ := (h.disjoint₁₃.mono Set.inter_subset_left Set.inter_subset_left)
  disjoint₂₃ := (h.disjoint₂₃.mono Set.inter_subset_left Set.inter_subset_left)

end PartitionInter

/-! ### The Gaussian restricted to an arclength-parameterised needle -/

section GaussianNeedle

variable {n : ℕ}

/-- **A needle sees a one-dimensional Gaussian of the same variance.**

For a unit vector `e`, `‖p + t·e‖² = (t − t₀)² + (‖p‖² − t₀²)` with `t₀ = −⟪p,e⟫`.  Hence the
restriction of `N(0,σ²Iₙ)`'s density to the line `t ↦ p + t·e` is a constant multiple of the
one-dimensional density `exp(−(t − t₀)²/(2σ²))` — the *same* `σ`.  This is what lets the
one-dimensional inequality `(1d-2)`, whose constant comes from Brascamp–Lieb applied to a
variance-`σ²` Gaussian, be stated intrinsically in one dimension. -/
theorem norm_needleMap_sq (p e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) (t : ℝ) :
    ‖needleMap p e t‖ ^ 2
      = (t - -(inner ℝ p e)) ^ 2 + (‖p‖ ^ 2 - (inner ℝ p e) ^ 2) := by
  have h := norm_add_sq_real p (t • e)
  rw [needleMap]
  rw [h, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he]
  ring

/-- The Gaussian weight along an arclength-parameterised needle, factored as a constant times a
one-dimensional Gaussian of the same variance. -/
theorem gaussian_needleMap (p e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) {σ : ℝ} (hσ : 0 < σ)
    (t : ℝ) :
    Real.exp (-‖needleMap p e t‖ ^ 2 / (2 * σ ^ 2))
      = Real.exp (-(‖p‖ ^ 2 - (inner ℝ p e) ^ 2) / (2 * σ ^ 2))
          * Real.exp (-(t - -(inner ℝ p e)) ^ 2 / (2 * σ ^ 2)) := by
  rw [← Real.exp_add, norm_needleMap_sq p e he t]
  congr 1
  field_simp
  ring

end GaussianNeedle

/-! ### The theorem -/

section Main

variable {n : ℕ}

/-- **Cousins–Vempala, Theorem 3.4 (`thm:iso`, `vol3_journal.tex:467`), assembled.**

Let `π` be `N(0, σ²Iₙ)` restricted by a log-concave `f : ℝⁿ → ℝ₊`, i.e. `π` has density
proportional to `h(x) = f(x)·exp(−‖x‖²/2σ²)`.  Let `S₁, S₂, S₃` partition `ℝⁿ` so that for every
`u ∈ S₁` and `v ∈ S₂`,

* either `‖u − v‖ ≥ d / ln 2`,
* or `d_h(u,v) ≥ 4(d/σ)√n`.

Then `π(S₃) ≥ (d/σ)·π(S₁)·π(S₂)`, here in the division-free form
`(d/σ)·(∫_{S₁} h)(∫_{S₂} h) ≤ (∫ h)(∫_{S₃} h)`.

**Discrepancy with the printed statement.**  The paper prints the second branch as
`d_h(u,v) ≥ 4d√n`, with no `σ`.  That form is *not* what its own proof delivers: the proof
argues at `σ = 1` and then rescales by `x = y/σ`, under which the metric branch `‖u−v‖ ≥ d/ln 2`
is `σ`-covariant but `d_h` is scale-*invariant*.  Feeding the printed hypothesis through the
rescaling yields only `π(S₃) ≥ min{d, d/σ}·π(S₁)π(S₂)`, which is weaker than the printed
conclusion whenever `σ < 1` — exactly the regime Gaussian cooling runs in.  The corrected
disjunct `d_h(u,v) ≥ 4(d/σ)√n` is used here; see the module docstring for why the downstream
conductance bound of `vol3_journal.tex:647` is unaffected.

**The four hypotheses that are not geometry.**  `hloc`, `hcombinatorial`, `h1d1` and `h1d2` are
external inputs, each a plain binder documented at its declaration site; see the module
docstring for who is expected to discharge each. -/
theorem gaussianRestricted_isoperimetry (hn : 0 < n) {σ d : ℝ} (hσ : 0 < σ)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v)
    -- **(L)** The Localization Lemma of Lovász–Simonovits (KLS 1995, Corollary 2.4), applied
    -- to `g₁ = 1_{S₁}h − A·h` and `g₂ = (d/σ)A·1_{S₂}h − 1_{S₃}h`; `vol3_journal.tex:479–493`.
    -- The needle is arclength-parameterised (`‖e‖ = 1`); the paper's `(1−t)a + tb`, `t ∈ [0,1]`
    -- differs from it by an affine change of parameter, under which both displayed relations
    -- are invariant.  Partially assembled in `Arlib.Convexity.LocalizationAssembly`; see the
    -- module docstring for the residuals.
    (hloc : ∀ A : ℝ, 0 < A →
      (∫ x in S₁, h x) = A * ∫ x, h x →
      (∫ x in S₃, h x) < d / σ * A * ∫ x in S₂, h x →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (c₀ c₁ α β : ℝ),
        ‖e‖ = 1 ∧ α ≤ β ∧ (∀ t ∈ Set.Icc α β, 0 ≤ c₀ + c₁ * t) ∧
        IntervalIntegrable
          (fun t => (c₀ + c₁ * t) ^ (n - 1) * h (needleMap p e t)) volume α β ∧
        (∫ t in needleMap p e ⁻¹' S₁ ∩ Set.Icc α β,
            (c₀ + c₁ * t) ^ (n - 1) * h (needleMap p e t))
          = A * ∫ t in α..β, (c₀ + c₁ * t) ^ (n - 1) * h (needleMap p e t) ∧
        (∫ t in needleMap p e ⁻¹' S₃ ∩ Set.Icc α β,
            (c₀ + c₁ * t) ^ (n - 1) * h (needleMap p e t))
          < d / σ * A * ∫ t in needleMap p e ⁻¹' S₂ ∩ Set.Icc α β,
              (c₀ + c₁ * t) ^ (n - 1) * h (needleMap p e t))
    -- **(C)** "By a standard combinatorial argument, we can assume that the `Zᵢ` are intervals
    -- that partition `[a,b]`" — `vol3_journal.tex:497`.  Its *content* is the passage from the
    -- interval case of the one-dimensional isoperimetric inequality (hypothesis `hint`, which
    -- `h1d1`/`h1d2` supply) to an arbitrary measurable three-way partition (`hcross`, which the
    -- separation hypothesis supplies).  Stated for an arbitrary nonnegative weight `D` and an
    -- arbitrary symmetric coefficient function `κ`.
    --
    -- The separation input `hcross` is **not** removable: without it the statement is false.
    -- Take `D ≡ 1` on `[0,1]`, `Z₁ = [0,0.4] ∪ [0.6,1]`, `Z₂ = (0.45,0.5)`, `Z₃` the rest, and
    -- `c = 4`; then `∫_{Z₁} = 0.8`, `∫_{Z₂} = 0.05`, `∫_{Z₃} = 0.15 < c·0.8·0.05`, yet
    -- `c·(∫_{Z₁})(∫_{Z₂}) = 0.16 > 0.15`.  `hcross` fails there because the cross pair
    -- `(0.4, 0.45)` forces `c ≤ κ(0.4,0.45) ≤ 0.227` through `hint`.
    (hcombinatorial : ∀ (D : ℝ → ℝ) (Z₁ Z₂ Z₃ : Set ℝ) (κ : ℝ → ℝ → ℝ) (α β c : ℝ), α ≤ β →
      (∀ t ∈ Set.Icc α β, 0 ≤ D t) → IntervalIntegrable D volume α β →
      IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃ →
      MeasurableSet Z₁ → MeasurableSet Z₂ → MeasurableSet Z₃ →
      (∀ x y : ℝ, α ≤ x → x ≤ y → y ≤ β →
        κ x y * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
          ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t) →
      (∀ s ∈ Z₁, ∀ t ∈ Z₂, c ≤ κ (min s t) (max s t)) →
      c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t) ≤ (∫ t in α..β, D t) * ∫ t in Z₃, D t)
    -- **(1d-1)** `vol3_journal.tex:498`, cited there as Lemma 3.8 of KLS 1997.
    (h1d1 : ∀ (g l : ℝ → ℝ) (α β u v : ℝ), α ≤ u → u ≤ v → v ≤ β →
      (∀ t ∈ Set.Icc α β, 0 ≤ g t) → LogConcaveOn (Set.Icc α β) g →
      (∀ t ∈ Set.Icc α β, 0 ≤ l t) → (∃ c₀ c₁ : ℝ, ∀ t, l t = c₀ + c₁ * t) →
      IntervalIntegrable (fun t => l t ^ (n - 1) * g t) volume α β →
      densDist g u v * ((∫ t in α..u, l t ^ (n - 1) * g t) *
            (∫ t in v..β, l t ^ (n - 1) * g t))
        ≤ 4 * Real.sqrt n * ((∫ t in α..β, l t ^ (n - 1) * g t) *
            (∫ t in u..v, l t ^ (n - 1) * g t)))
    -- **(1d-2)** `vol3_journal.tex:501`, with the paper's coefficient `\iso = ln 2`, divided by
    -- `σ` because the needle's Gaussian factor has variance `σ²` rather than `1`.
    (h1d2 : ∀ (F : ℝ → ℝ) (t₀ α β u v : ℝ), α ≤ u → u ≤ v → v ≤ β →
      (∀ t ∈ Set.Icc α β, 0 ≤ F t) → LogConcaveOn (Set.Icc α β) F →
      IntervalIntegrable (fun t => F t * Real.exp (-(t - t₀) ^ 2 / (2 * σ ^ 2))) volume α β →
      Real.log 2 / σ * (v - u) *
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
  -- localisation
  obtain ⟨p, e, c₀, c₁, α, β, he1, hαβ, hlnn, hint, hZ1, hZ3⟩ := hloc A hApos rel1 rel2
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := needleMap p e with hγ
  set D : ℝ → ℝ := fun t => (c₀ + c₁ * t) ^ (n - 1) * h (γ t) with hD
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
  set F : ℝ → ℝ := fun t => K * ((c₀ + c₁ * t) ^ (n - 1) * f (γ t)) with hF
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
        (logConcaveOn_pow_of_concaveOn (concaveOn_affine_real (convex_Icc α β) c₀ c₁)
          (fun _ ht => hlnn _ ht) (n - 1))
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
      (Real.log 2 / σ * (y - x)) with hκ
  have hκ1 : ∀ x y : ℝ, α ≤ x → x ≤ y → y ≤ β →
      κ x y * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
        ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t := by
    intro x y hx hxy hy
    have hL : 0 ≤ ∫ t in α..x, D t :=
      intervalIntegral.integral_nonneg hx fun t ht =>
        hD0 t ⟨ht.1, ht.2.trans (hxy.trans hy)⟩
    have hR : 0 ≤ ∫ t in y..β, D t :=
      intervalIntegral.integral_nonneg hy fun t ht =>
        hD0 t ⟨(hx.trans hxy).trans ht.1, ht.2⟩
    have hone := h1d1 (fun t => h (γ t)) (fun t => c₀ + c₁ * t) α β x y hx hxy hy hg0 hgc
      hlnn ⟨c₀, c₁, fun _ => rfl⟩ hint
    have htwo := h1d2 F t₀ α β x y hx hxy hy hF0 hFc hintF
    simp only [hFD] at htwo
    exact oneDimCoeff_mul_le hn (mul_nonneg hL hR) hone htwo
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
    exact le_oneDimCoeff_of_sep hn hσ hsep'
  -- the one-dimensional isoperimetric inequality for the induced partition
  have hiso := hcombinatorial D _ _ _ κ α β (d / σ) hαβ hD0 hint hpart' hmZ1 hmZ2 hmZ3 hκ1 hκ2
  exact needle_masses_contradiction hIpos hZ1 hZ3 hiso

end Main

/-! ### Non-vacuity: the geometric hypotheses hold together, with a positive right-hand side -/

section Witness

variable {n : ℕ}

/-- **The metric branch of the separation hypothesis, for a slab.**  If `e` is a unit vector and
`⟪e,u⟫ < −c < c < ⟪e,v⟫`, then `‖u − v‖ ≥ 2c`. -/
theorem two_mul_le_norm_sub_of_inner_lt {e u v : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    {c : ℝ} (hu : inner ℝ e u < -c) (hv : c < inner ℝ e v) : 2 * c ≤ ‖u - v‖ := by
  rcases le_or_gt c 0 with hc | hc
  · linarith [norm_nonneg (u - v)]
  · have h := abs_real_inner_le_norm e (u - v)
    rw [he, one_mul, inner_sub_right] at h
    have h2 : 2 * c ≤ |(inner ℝ e u : ℝ) - inner ℝ e v| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    linarith

/-- **The slab partition.**  For a unit vector `e` and `c > 0`, the two open half-spaces
`⟪e,x⟫ < −c` and `⟪e,x⟫ > c` together with the closed slab between them partition `ℝⁿ`. -/
theorem isPartition3_slab (e : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc0 : 0 ≤ c) :
    IsPartition3 Set.univ {x | inner ℝ e x < -c} {x | c < inner ℝ e x}
      {x | -c ≤ inner ℝ e x ∧ (inner ℝ e x : ℝ) ≤ c} where
  union := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rcases lt_or_ge (inner ℝ e x : ℝ) (-c) with h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_or_ge c (inner ℝ e x : ℝ) with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨h, h'⟩
  disjoint₁₂ := by
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith
  disjoint₁₃ := by
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith [hx'.1]
  disjoint₂₃ := by
    rw [Set.disjoint_left]
    rintro x hx hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    linarith [hx'.2]

/-- A nonnegative integrable function bounded below by `c > 0` on a ball contained in `S` has
positive integral over `S`. -/
theorem setIntegral_pos_of_ball_le {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Integrable g)
    (hg0 : ∀ x, 0 ≤ g x) {S : Set (EuclideanSpace ℝ (Fin n))}
    {z : EuclideanSpace ℝ (Fin n)} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hball : Metric.ball z r ⊆ S) (hlow : ∀ x ∈ Metric.ball z r, c ≤ g x) :
    0 < ∫ x in S, g x := by
  have h1 : c * volume.real (Metric.ball z r) ≤ ∫ x in Metric.ball z r, g x :=
    setIntegral_ge_of_const_le_real measurableSet_ball measure_ball_lt_top.ne hlow
      hg.integrableOn
  have hvol : 0 < volume.real (Metric.ball z r) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume z hr).ne' measure_ball_lt_top.ne
  have h3 : (∫ x in Metric.ball z r, g x) ≤ ∫ x in S, g x :=
    setIntegral_mono_set hg.integrableOn (Filter.Eventually.of_forall hg0)
      hball.eventuallyLE
  nlinarith

/-- **Non-vacuity witness for `Arlib.gaussianRestricted_isoperimetry`.**

Every geometric hypothesis of the theorem is satisfiable simultaneously, at parameters where
its conclusion is a *strictly positive* lower bound (so the statement is not the trivial
`0 ≤ something`).  The instance is `σ = 1`, `f` the indicator of the unit ball — a log-concave
function, so `h = f·γ` is the Gaussian restricted to the unit ball — `d = (ln 2)/2`, and
`S₁, S₂, S₃` the slab partition of width `1/2` orthogonal to the first coordinate axis.  The
metric branch of the separation hypothesis is what holds here; the density branch is never
needed (and, by `Arlib.densDist_le_one`, is unsatisfiable once `4d√n/σ > 1`).

The four external inputs `hloc`, `hintervals`, `h1d1`, `h1d2` are not part of the witness: they
are universally quantified statements of the literature, not properties of this instance.  At
this instance `hloc`'s antecedent is in fact unsatisfiable (its conclusion holds), so it too is
satisfied here — vacuously. -/
theorem gaussianRestricted_isoperimetry_witness (hn : 0 < n) :
    ∃ (f h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d : ℝ),
      0 < σ ∧ 0 < d ∧ (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧
      (∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (0 < ∫ x, h x) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) ∧
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
  have hint : Integrable h := by
    rw [hheq]
    refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
    exact hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)
  -- the ball around `r • e` of radius `1/8` sits inside the unit ball, on the `r` side of the
  -- slab, and `h` is at least `e^{-1/2}` there
  have hballs : ∀ r : ℝ, |r| = 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1/8),
      ‖x‖ ≤ 1 ∧ |(inner ℝ e x : ℝ) - r| < 1/8 := by
    intro r hr x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hre : ‖r • e‖ = 1 / 2 := by rw [norm_smul, Real.norm_eq_abs, hr, he, mul_one]
    constructor
    · have : ‖x‖ ≤ ‖x - r • e‖ + ‖r • e‖ := by
        simpa using norm_add_le (x - r • e) (r • e)
      rw [hre] at this
      linarith
    · have hip := abs_real_inner_le_norm e (x - r • e)
      rw [he, one_mul, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, he] at hip
      simpa using hip.trans_lt hx
  have hlow : ∀ r : ℝ, |r| = 1 / 2 → ∀ x ∈ Metric.ball (r • e) (1/8),
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
  refine ⟨f, h, {x | inner ℝ e x < -(1/4 : ℝ)}, {x | (1/4 : ℝ) < inner ℝ e x},
    {x | -(1/4 : ℝ) ≤ inner ℝ e x ∧ (inner ℝ e x : ℝ) ≤ 1/4}, 1, Real.log 2 / 2,
    one_pos, by positivity, hf0, hfc, fun x => by simp only [hhdef],
    isPartition3_slab e (by norm_num : (0:ℝ) ≤ 1/4), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact measurableSet_lt hme measurable_const
  · exact measurableSet_lt measurable_const hme
  · exact (measurableSet_le measurable_const hme).inter (measurableSet_le hme measurable_const)
  · -- total mass is positive
    have hpos := setIntegral_pos_of_ball_le (z := ((1/2 : ℝ) • e)) (r := 1/8)
      (c := Real.exp (-(1:ℝ)/2)) hint h0 (by norm_num) (Real.exp_pos _) (Set.subset_univ _)
      (hlow (1/2) (by norm_num))
    rwa [setIntegral_univ] at hpos
  · -- separation: the metric branch
    intro u hu v hv
    left
    have := two_mul_le_norm_sub_of_inner_lt (e := e) he (c := (1/4 : ℝ)) hu hv
    have hlog : Real.log 2 / 2 / Real.log 2 = 1 / 2 := by
      field_simp
    rw [hlog]
    linarith
  · -- the right-hand side is strictly positive
    have hp1 : 0 < ∫ x in {x | inner ℝ e x < -(1/4 : ℝ)}, h x := by
      refine setIntegral_pos_of_ball_le (z := (-(1/2 : ℝ) • e)) (r := 1/8)
        (c := Real.exp (-(1:ℝ)/2)) hint h0 (by norm_num) (Real.exp_pos _) ?_
        (hlow (-(1/2)) (by norm_num))
      intro x hx
      obtain ⟨-, hx2⟩ := hballs (-(1/2)) (by norm_num) x hx
      simp only [Set.mem_setOf_eq]
      rw [abs_lt] at hx2
      linarith [hx2.2]
    have hp2 : 0 < ∫ x in {x | (1/4 : ℝ) < inner ℝ e x}, h x := by
      refine setIntegral_pos_of_ball_le (z := ((1/2 : ℝ) • e)) (r := 1/8)
        (c := Real.exp (-(1:ℝ)/2)) hint h0 (by norm_num) (Real.exp_pos _) ?_
        (hlow (1/2) (by norm_num))
      intro x hx
      obtain ⟨-, hx2⟩ := hballs (1/2) (by norm_num) x hx
      simp only [Set.mem_setOf_eq]
      rw [abs_lt] at hx2
      linarith [hx2.1]
    have hd : (0:ℝ) < Real.log 2 / 2 / 1 := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 2)
      positivity
    exact mul_pos hd (mul_pos hp1 hp2)

end Witness

end Arlib

/-! ### Axiom audit

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Arlib.needle_masses_contradiction
#print axioms Arlib.oneDimCoeff_mul_le
#print axioms Arlib.le_oneDimCoeff_of_sep
#print axioms Arlib.isPartition3_inter
#print axioms Arlib.norm_needleMap_sq
#print axioms Arlib.gaussian_needleMap
#print axioms Arlib.gaussianRestricted_isoperimetry
#print axioms Arlib.two_mul_le_norm_sub_of_inner_lt
#print axioms Arlib.isPartition3_slab
#print axioms Arlib.setIntegral_pos_of_ball_le
#print axioms Arlib.gaussianRestricted_isoperimetry_witness
