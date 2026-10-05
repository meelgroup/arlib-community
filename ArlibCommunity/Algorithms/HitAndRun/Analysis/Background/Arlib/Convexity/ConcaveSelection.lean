/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Data.Rat.Denumerable
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.NeedleProfile

/-!
# (G2a) and (G2b): profile selection and the uniform profile bound

`Arlib.Convexity.NeedleProfile` §3 listed exactly three residual items of gap **(G2)**, all of
them inline `∀`-hypotheses of `Arlib.tendsto_average_setIntegral_of_profile`.  **This file
proves (G2a) and (G2b).**  (G2c) — the affine change of coordinates carrying a general segment
to the first axis — is *not* proved here; see §4.

## 1. (G2a): pointwise selection, proved

`Arlib.exists_subseq_tendsto_normalised_slice_profile` — given convex measurable bodies `C k` of
finite positive volume, contained in and spanning the unit slab, with slices of finite volume
and uniformly bounded normalised profiles, some **subsequence** of the normalised slice profiles
`t ↦ vol (slice (C k) t) / vol (C k)` converges **at every real number**.

The framing is the one that makes it tractable: not Blaschke selection on bodies, but
Arzelà–Ascoli on the profiles.  By `Arlib.brunn_slice_concaveOn` the `1/m`-th roots of the
profiles are concave, hence equi-Lipschitz on every `[c, 1-c]` with constant `2M/c` depending
only on the uniform bound `M` and on `c` (`Arlib.abs_sub_le_of_concaveOn_Ioo`).

**Mathlib has no sequence-level Arzelà–Ascoli and no Helly selection theorem.**  What it has is
`ArzelaAscoli.isCompact_of_equicontinuous` / `BoundedContinuousFunction.arzela_ascoli`
(compactness of a closure in a function space) and `IsCompact.tendsto_subseq` (subsequence
extraction from a compact set in a first-countable space).  Rather than build the function-space
plumbing, this file runs the argument directly:

* `Arlib.exists_subseq_tendsto_of_concaveOn_Ioo` — the abstract selection theorem.  Sequential
  compactness of `∏_{n : ℕ} [0, M]` (`isCompact_univ_pi` + `IsCompact.tendsto_subseq`, available
  because the product uniformity over a countable index is countably generated) extracts, in
  **one** step, a subsequence converging at every rational simultaneously; equi-Lipschitzness
  turns that into a Cauchy sequence at every point of `(0,1)`.

## 2. The endpoints — resolved, not papered over

Concave functions on `[0,1]` are equicontinuous only on compact *subintervals*, and the
Lipschitz constant `2M/c` genuinely blows up as `c → 0`.  The limit profile `W` produced here
**need not be continuous at `0` or at `1`**, and none is claimed.

This costs nothing, because the consumer
`Arlib.tendsto_average_setIntegral_of_profile` uses the profile hypothesis only through
`tendsto_integral_of_dominated_convergence`: it needs **pointwise convergence and a uniform
bound**, never continuity or uniform convergence.  So the endpoints only have to be *reached*,
not reached continuously — and they are, for free: `0` and `1` are rational, so the single
extraction over `ℚ` already fixes their limits.  Off `[0,1]` the profiles are identically `0`.

Consequently the theorem proved here is exactly the missing hypothesis, with no weakening, and
`Arlib.exists_subseq_tendsto_average_setIntegral` discharges it into the consumer.

## 3. (G2b): the uniform bound, proved

`Arlib.normalised_volume_slice_le` — `vol (slice C t) ≤ 2^(m+1) · vol C` for every `t`, for
every convex measurable `C` in the unit slab whose slices are nonempty and finite-volume at
every height of the *closed* interval `[0,1]`.  The constant is uniform over all such `C`.

The mechanism is the one the `NeedleProfile` docstring predicted, threaded (as it said it must
be) through the measurable slice profile rather than through an abstract `ConcaveOn`: by
`Arlib.half_le_of_concaveOn_Icc`, a nonnegative concave `u` on `[0,1]` satisfies `u ≥ u(t)/2` on
`[t/2, (1+t)/2]`, an interval of length `1/2` *independent of `t`*; integrating `u^m` there
against `Arlib.integral_volume_slice` gives `(u t/2)^m / 2 ≤ vol C`.  (This is sharper than the
`4·2^m` the docstring anticipated, and needs no case split on which side of `1/2` the maximum
lies.)  Integrability of the profile is automatic: it is nonnegative with integral `vol C > 0`,
and a non-integrable function has Bochner integral `0`.

`Arlib.exists_subseq_tendsto_average_setIntegral'` is the consumer with **both** (G2a) and (G2b)
discharged.

## 4. What is left of (G2)

**(G2c) is not proved here.**  Everything above, like `Arlib.Convexity.NeedleProfile`, is stated
with the needle along the first coordinate axis and the slab `{x | x 0 ∈ [0,1]}`.  Carrying a
general segment `[a,b] ⊆ ℝⁿ` there needs (i) the transformation rule for `volume` under an
affine equivalence of `Fin n → ℝ` (`Measure.addHaar_preimage_linearMap`) and (ii) — the part
that is not routine in a formal setting — a compatible statement for the `(n-1)`-dimensional
slice volumes, i.e. a factorisation of the determinant into the first-coordinate scaling and
the transverse determinant, so that Fubini in the rotated frame lines up with
`Arlib.setIntegral_eq_integral_slice`.  The transverse factor cancels in the *normalised*
profile, so only the first-coordinate scaling survives into the limit; but that cancellation
still has to be proved.

Two hypotheses of this file are worth naming explicitly, since they are additions to the list in
`NeedleProfile` §3 rather than consequences of it:

* `hsfin : ∀ t, volume (slice C t) ≠ ⊤` — needed by `Arlib.brunn_slice_concaveOn`, and
  discharged for any body contained in a box by `Arlib.volume_slice_ne_top_of_forall_abs_le`.
* `hspan` — the bodies must *span* the slab (nonempty slices at every height).  (G2a) needs this
  only on the open interval `(0,1)`; (G2b) needs it on the closed `[0,1]`.  This is what an
  affine normalisation of the first coordinate would supply, and it is the reason the two are
  stated separately.

## Honesty note

This file contains **no** `def`, `structure`, `class` or named `Prop` — only theorems proved
outright.  Nothing here asserts the Localization Lemma, Blaschke selection, or a
profile-convergence property.  Non-vacuity of the hypothesis bundle is witnessed by
`Arlib.exists_subseq_tendsto_normalised_slice_profile_unitCube`, which also checks that the
limit profile produced is **nonzero**.
-/

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Topology

namespace Arlib

/-! ### Equi-Lipschitz bounds for bounded concave functions on `(0,1)` -/

section ConcaveSlope

variable {u : ℝ → ℝ}

/-- **Right increments of a bounded nonnegative concave function are controlled.**
If `u` is concave on `(0,1)` with `0 ≤ u ≤ M`, then for `c ≤ x < y ≤ 1 - c` the increment
`u y - u x` is at most `(2M/c)(y - x)`.  The comparison point is `c/2`, to the left of `x`. -/
theorem sub_le_of_concaveOn_Ioo_right (hu : ConcaveOn ℝ (Ioo (0:ℝ) 1) u) (hu0 : ∀ t, 0 ≤ u t)
    {M : ℝ} (hM0 : 0 ≤ M) (huM : ∀ t, u t ≤ M) {c x y : ℝ} (hc : 0 < c) (hc2 : c < 1/2)
    (hcx : c ≤ x) (hxy : x < y) (hy1 : y ≤ 1 - c) :
    u y - u x ≤ 2 * M / c * (y - x) := by
  have hzI : (c / 2) ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hyI : y ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hyz : (0:ℝ) < y - c / 2 := by linarith
  set lam : ℝ := (y - x) / (y - c / 2) with hlamdef
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) (by linarith)
  have hlam1 : lam ≤ 1 := (div_le_one hyz).mpr (by linarith)
  have hd : y - c / 2 ≠ 0 := ne_of_gt hyz
  have hkey : lam * (y - c / 2) = y - x := by
    rw [hlamdef, div_mul_eq_mul_div, mul_div_assoc, div_self hd, mul_one]
  have hcomb : lam • (c / 2) + (1 - lam) • y = x := by
    simp only [smul_eq_mul]; linear_combination -hkey
  have hconc := hu.2 hzI hyI hlam0 (by linarith : (0:ℝ) ≤ 1 - lam) (by ring)
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hconc
  have h1 : u y - u x ≤ lam * u y := by
    nlinarith [mul_nonneg hlam0 (hu0 (c / 2))]
  have h2 : lam ≤ 2 * (y - x) / c := by
    rw [hlamdef, div_le_div_iff₀ hyz hc]
    nlinarith [mul_nonneg (sub_pos.mpr hxy).le (show (0:ℝ) ≤ y - c by linarith)]
  calc u y - u x ≤ lam * u y := h1
    _ ≤ lam * M := mul_le_mul_of_nonneg_left (huM y) hlam0
    _ ≤ 2 * (y - x) / c * M := mul_le_mul_of_nonneg_right h2 hM0
    _ = 2 * M / c * (y - x) := by ring

/-- **Left increments of a bounded nonnegative concave function are controlled.**
The mirror image of `Arlib.sub_le_of_concaveOn_Ioo_right`; the comparison point is `1 - c/2`,
to the right of `y`. -/
theorem sub_le_of_concaveOn_Ioo_left (hu : ConcaveOn ℝ (Ioo (0:ℝ) 1) u) (hu0 : ∀ t, 0 ≤ u t)
    {M : ℝ} (hM0 : 0 ≤ M) (huM : ∀ t, u t ≤ M) {c x y : ℝ} (hc : 0 < c) (hc2 : c < 1/2)
    (hcx : c ≤ x) (hxy : x < y) (hy1 : y ≤ 1 - c) :
    u x - u y ≤ 2 * M / c * (y - x) := by
  have hzI : (1 - c / 2) ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hxI : x ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hzx : (0:ℝ) < (1 - c / 2) - x := by linarith
  set mu : ℝ := (y - x) / ((1 - c / 2) - x) with hmudef
  have hmu0 : 0 ≤ mu := div_nonneg (by linarith) (by linarith)
  have hmu1 : mu ≤ 1 := (div_le_one hzx).mpr (by linarith)
  have hd : (1 - c / 2) - x ≠ 0 := ne_of_gt hzx
  have hkey : mu * ((1 - c / 2) - x) = y - x := by
    rw [hmudef, div_mul_eq_mul_div, mul_div_assoc, div_self hd, mul_one]
  have hcomb : mu • (1 - c / 2) + (1 - mu) • x = y := by
    simp only [smul_eq_mul]; linear_combination hkey
  have hconc := hu.2 hzI hxI hmu0 (by linarith : (0:ℝ) ≤ 1 - mu) (by ring)
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hconc
  have h1 : u x - u y ≤ mu * u x := by
    nlinarith [mul_nonneg hmu0 (hu0 (1 - c / 2))]
  have h2 : mu ≤ 2 * (y - x) / c := by
    rw [hmudef, div_le_div_iff₀ hzx hc]
    nlinarith [mul_nonneg (sub_pos.mpr hxy).le (show (0:ℝ) ≤ 1 - c - x by linarith)]
  calc u x - u y ≤ mu * u x := h1
    _ ≤ mu * M := mul_le_mul_of_nonneg_left (huM x) hmu0
    _ ≤ 2 * (y - x) / c * M := mul_le_mul_of_nonneg_right h2 hM0
    _ = 2 * M / c * (y - x) := by ring

/-- **A nonnegative concave function on `(0,1)` bounded by `M` is `2M/c`-Lipschitz on
`[c, 1-c]`.**  The constant depends only on `M` and `c` — *not* on `u` — which is exactly the
equicontinuity needed for an Arzelà–Ascoli argument.  The blow-up as `c → 0` is genuine: this
is why the endpoints of `[0,1]` have to be handled separately. -/
theorem abs_sub_le_of_concaveOn_Ioo (hu : ConcaveOn ℝ (Ioo (0:ℝ) 1) u) (hu0 : ∀ t, 0 ≤ u t)
    {M : ℝ} (hM0 : 0 ≤ M) (huM : ∀ t, u t ≤ M) {c : ℝ} (hc : 0 < c) (hc2 : c < 1/2)
    {x y : ℝ} (hx : x ∈ Icc c (1 - c)) (hy : y ∈ Icc c (1 - c)) :
    |u x - u y| ≤ 2 * M / c * |x - y| := by
  rcases lt_trichotomy x y with h | h | h
  · rw [abs_sub_le_iff]
    have hxy : |x - y| = y - x := by rw [abs_sub_comm, abs_of_pos (by linarith)]
    rw [hxy]
    exact ⟨sub_le_of_concaveOn_Ioo_left hu hu0 hM0 huM hc hc2 hx.1 h hy.2,
      sub_le_of_concaveOn_Ioo_right hu hu0 hM0 huM hc hc2 hx.1 h hy.2⟩
  · subst h; simp
  · rw [abs_sub_le_iff]
    have hxy : |x - y| = x - y := abs_of_pos (by linarith)
    rw [hxy]
    exact ⟨sub_le_of_concaveOn_Ioo_right hu hu0 hM0 huM hc hc2 hy.1 h hx.2,
      sub_le_of_concaveOn_Ioo_left hu hu0 hM0 huM hc hc2 hy.1 h hx.2⟩

/-- **A nonnegative concave function on `[0,1]` is at least half its value at `t` throughout
the interval `[t/2, (1+t)/2]`,** which has length `1/2` *independently of `t`*.

To the left of `t` compare with the endpoint `0`, to the right with the endpoint `1`; in both
cases the barycentric weight of `t` is at least `1/2` on the stated range.  This is the
elementary ingredient of (G2b). -/
theorem half_le_of_concaveOn_Icc (hu : ConcaveOn ℝ (Icc (0:ℝ) 1) u)
    (hu0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ u x) {t r : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hr1 : t / 2 ≤ r) (hr2 : r ≤ (1 + t) / 2) :
    u t / 2 ≤ u r := by
  obtain ⟨ht0, ht1⟩ := ht
  have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht0, ht1⟩
  have h0I : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  have h1I : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num, le_refl 1⟩
  have hrI : r ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hst : 0 ≤ u t := hu0 t htI
  rcases lt_trichotomy r t with h | h | h
  · have ht0' : (0:ℝ) < t := by linarith
    have htne : t ≠ 0 := ne_of_gt ht0'
    set lam : ℝ := r / t with hlamdef
    have hlam0 : 0 ≤ lam := div_nonneg hrI.1 ht0'.le
    have hlam1 : lam ≤ 1 := (div_le_one ht0').mpr h.le
    have hkey : lam * t = r := by
      rw [hlamdef, div_mul_eq_mul_div, mul_div_assoc, div_self htne, mul_one]
    have hcomb : lam • t + (1 - lam) • (0:ℝ) = r := by
      simp only [smul_eq_mul]; linear_combination hkey
    have hc := hu.2 htI h0I hlam0 (by linarith : (0:ℝ) ≤ 1 - lam) (by ring)
    rw [hcomb, smul_eq_mul, smul_eq_mul] at hc
    have hhalf : (1:ℝ) / 2 ≤ lam := by rw [hlamdef, le_div_iff₀ ht0']; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf) hst,
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) (hu0 0 h0I)]
  · subst h; linarith
  · have ht1' : t < 1 := by linarith
    have hden : (0:ℝ) < 1 - t := by linarith
    set lam : ℝ := (1 - r) / (1 - t) with hlamdef
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hden.le
    have hlam1 : lam ≤ 1 := (div_le_one hden).mpr (by linarith)
    have hkey : lam * (1 - t) = 1 - r := by
      rw [hlamdef, div_mul_eq_mul_div, mul_div_assoc, div_self hden.ne', mul_one]
    have hcomb : lam • t + (1 - lam) • (1:ℝ) = r := by
      simp only [smul_eq_mul]; linear_combination -hkey
    have hc := hu.2 htI h1I hlam0 (by linarith : (0:ℝ) ≤ 1 - lam) (by ring)
    rw [hcomb, smul_eq_mul, smul_eq_mul] at hc
    have hhalf : (1:ℝ) / 2 ≤ lam := by rw [hlamdef, le_div_iff₀ hden]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf) hst,
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) (hu0 1 h1I)]

end ConcaveSlope

/-! ### The selection theorem -/

/-- **Arzelà–Ascoli/Helly selection for a uniformly bounded sequence of concave functions.**

Let `u k` be nonnegative functions on `ℝ`, uniformly bounded by `M`, each concave on the *open*
interval `(0,1)` and vanishing outside `[0,1]`.  Then some subsequence converges **pointwise at
every real number** to a limit `V`.

The proof is Arzelà–Ascoli done by hand:
* `Arlib.abs_sub_le_of_concaveOn_Ioo` gives equi-Lipschitz constants on every `[c, 1-c]`;
* a single application of sequential compactness of `∏_{n : ℕ} [0, M]`
  (`isCompact_univ_pi` + `IsCompact.tendsto_subseq`, legitimate because the product uniformity
  over a countable index is countably generated) extracts one subsequence converging at *every
  rational* at once;
* equi-Lipschitzness upgrades this to a Cauchy, hence convergent, sequence at every
  `t ∈ (0,1)`;
* the two endpoints `0` and `1` are themselves rational, so they are covered by the same
  extraction — **no continuity of `V` at the endpoints is claimed or needed**;
* off `[0,1]` the sequence is identically `0`.

`V` need not be continuous at `0` or `1`, and in general is not: only pointwise convergence is
asserted. -/
theorem exists_subseq_tendsto_of_concaveOn_Ioo {u : ℕ → ℝ → ℝ}
    (hconc : ∀ k, ConcaveOn ℝ (Ioo (0:ℝ) 1) (u k)) (hu0 : ∀ k t, 0 ≤ u k t)
    {M : ℝ} (huM : ∀ k t, u k t ≤ M)
    (hoff : ∀ k, ∀ t : ℝ, t ∉ Icc (0:ℝ) 1 → u k t = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : ℝ → ℝ,
      ∀ t : ℝ, Tendsto (fun k => u (φ k) t) atTop (𝓝 (V t)) := by
  have hM0 : (0 : ℝ) ≤ M := (hu0 0 0).trans (huM 0 0)
  -- Extract a subsequence converging at every rational, via compactness of `∏_{n} [0, M]`.
  set E : ℕ → ℝ := fun n => (((Denumerable.eqv ℚ).symm n : ℚ) : ℝ) with hE
  have hmem : ∀ k, (fun n => u k (E n)) ∈ Set.univ.pi fun _ : ℕ => Icc (0:ℝ) M :=
    fun k => Set.mem_univ_pi.mpr fun n => ⟨hu0 k _, huM k _⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ : ℕ => isCompact_Icc (a := (0:ℝ)) (b := M)).tendsto_subseq hmem
  have hlimn : ∀ n : ℕ, Tendsto (fun k => u (φ k) (E n)) atTop (𝓝 (a n)) :=
    fun n => tendsto_pi_nhds.mp hlim n
  have hrat : ∀ q : ℚ, ∃ L : ℝ, Tendsto (fun k => u (φ k) (q : ℝ)) atTop (𝓝 L) := by
    intro q
    refine ⟨a (Denumerable.eqv ℚ q), ?_⟩
    simpa only [hE, Equiv.symm_apply_apply] using hlimn (Denumerable.eqv ℚ q)
  -- Pointwise convergence at every real number.
  have hconv : ∀ t : ℝ, ∃ L : ℝ, Tendsto (fun k => u (φ k) t) atTop (𝓝 L) := by
    intro t
    by_cases ht : t ∈ Ioo (0:ℝ) 1
    · -- interior: equi-Lipschitz + convergence at nearby rationals ⟹ Cauchy
      obtain ⟨ht0, ht1⟩ := ht
      set c : ℝ := min t (1 - t) / 2 with hcdef
      have hc : 0 < c := by
        rw [hcdef]; have : 0 < min t (1 - t) := lt_min ht0 (by linarith); linarith
      have hct : c < t := by
        rw [hcdef]; have : min t (1 - t) ≤ t := min_le_left _ _; linarith
      have hct' : t < 1 - c := by
        rw [hcdef]; have : min t (1 - t) ≤ 1 - t := min_le_right _ _; linarith
      have hc2 : c < 1 / 2 := by linarith
      set K : ℝ := 2 * M / c with hKdef
      have hK0 : 0 ≤ K := by rw [hKdef]; positivity
      apply cauchySeq_tendsto_of_complete
      rw [Metric.cauchySeq_iff]
      intro ε hε
      set η : ℝ := min (t - c) (ε / (3 * (K + 1))) with hηdef
      have hη : 0 < η := by
        rw [hηdef]
        refine lt_min (by linarith) ?_
        positivity
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t - η < t by linarith)
      have hηa : η ≤ t - c := by rw [hηdef]; exact min_le_left _ _
      have hηb : η ≤ ε / (3 * (K + 1)) := by rw [hηdef]; exact min_le_right _ _
      have hqmem : (q : ℝ) ∈ Icc c (1 - c) := ⟨by linarith, by linarith⟩
      have htmem : t ∈ Icc c (1 - c) := ⟨le_of_lt hct, le_of_lt hct'⟩
      have hnear : ∀ k : ℕ, |u (φ k) t - u (φ k) (q : ℝ)| ≤ K * η := by
        intro k
        refine le_trans (abs_sub_le_of_concaveOn_Ioo (hconc (φ k)) (hu0 (φ k)) hM0
          (huM (φ k)) hc hc2 htmem hqmem) ?_
        have : |t - (q : ℝ)| ≤ η := by
          rw [abs_of_pos (by linarith : (0:ℝ) < t - (q:ℝ))]; linarith
        exact mul_le_mul_of_nonneg_left this hK0
      have hKη : K * η ≤ ε / 3 := by
        have h1 : K * η ≤ K * (ε / (3 * (K + 1))) := mul_le_mul_of_nonneg_left hηb hK0
        have h2 : K * (ε / (3 * (K + 1))) ≤ ε / 3 := by
          rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 3)]
          nlinarith [hε.le, hK0]
        linarith
      obtain ⟨L, hL⟩ := hrat q
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hL.cauchySeq (ε / 3) (by linarith)
      refine ⟨N, fun j hj i hi => ?_⟩
      have h1 := hnear j
      have h2 := hnear i
      have h3 := hN j hj i hi
      rw [Real.dist_eq] at h3 ⊢
      calc |u (φ j) t - u (φ i) t|
          ≤ |u (φ j) t - u (φ j) (q:ℝ)| + |u (φ j) (q:ℝ) - u (φ i) (q:ℝ)|
              + |u (φ i) (q:ℝ) - u (φ i) t| := by
            have := abs_sub_le (u (φ j) t) (u (φ j) (q:ℝ)) (u (φ i) t)
            have h4 := abs_sub_le (u (φ j) (q:ℝ)) (u (φ i) (q:ℝ)) (u (φ i) t)
            linarith
        _ < ε := by
            have h5 : |u (φ i) (q:ℝ) - u (φ i) t| = |u (φ i) t - u (φ i) (q:ℝ)| := abs_sub_comm _ _
            rw [h5]; linarith
    · -- boundary and exterior
      rcases eq_or_ne t 0 with rfl | h0
      · obtain ⟨L, hL⟩ := hrat 0
        exact ⟨L, by simpa using hL⟩
      rcases eq_or_ne t 1 with rfl | h1
      · obtain ⟨L, hL⟩ := hrat 1
        exact ⟨L, by simpa using hL⟩
      · refine ⟨0, ?_⟩
        have hnot : t ∉ Icc (0:ℝ) 1 := by
          intro hmem'
          exact ht ⟨lt_of_le_of_ne hmem'.1 (Ne.symm h0), lt_of_le_of_ne hmem'.2 h1⟩
        have : (fun k => u (φ k) t) = fun _ => (0:ℝ) := by
          funext k; exact hoff (φ k) t hnot
        rw [this]
        exact tendsto_const_nhds
  choose V hV using hconv
  exact ⟨φ, hφ, V, hV⟩

/-! ### (G2a): pointwise selection for normalised slice profiles -/

section SliceProfile

variable {m : ℕ}

/-- **The slice hypothesis `hsfin` is discharged for any body inside a box.**
If every coordinate of every point of `C` is bounded by `R` in absolute value, then every slice
has finite volume.  Every bounded body is of this form, so `hsfin` below is not a hidden
restriction. -/
theorem volume_slice_ne_top_of_forall_abs_le {C : Set (Fin (m + 1) → ℝ)} {R : ℝ}
    (hC : ∀ x ∈ C, ∀ i, |x i| ≤ R) (t : ℝ) : volume (slice C t) ≠ ⊤ := by
  have hsub : slice C t ⊆ Set.univ.pi fun _ : Fin m => Icc (-R) R := by
    intro y hy
    refine Set.mem_univ_pi.mpr fun j => ?_
    have h := hC _ (show (Fin.cons t y : Fin (m + 1) → ℝ) ∈ C from hy) j.succ
    rw [Fin.cons_succ] at h
    exact abs_le.mp h
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [volume_pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-- **(G2a), proved: a Helly/Arzelà–Ascoli selection for normalised slice profiles.**

Let `C k` be convex measurable bodies of finite positive volume, all contained in the unit slab
`{x | x 0 ∈ [0,1]}`, all *spanning* it (every height in `(0,1)` gives a nonempty slice) and all
with slices of finite volume, and suppose the normalised profiles are uniformly bounded by `B`.
Then some subsequence of the normalised slice profiles
`t ↦ vol (slice (C k) t) / vol (C k)` converges **at every real number**.

This is exactly the hypothesis `hlim` of `Arlib.tendsto_average_setIntegral_of_profile`, for the
subsequence `C ∘ φ`.

The proof passes to the `1/m`-th roots, which are concave by
`Arlib.brunn_slice_concaveOn`, applies `Arlib.exists_subseq_tendsto_of_concaveOn_Ioo`, and
raises back to the `m`-th power. -/
theorem exists_subseq_tendsto_normalised_slice_profile (hm : m ≠ 0)
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hconv : ∀ k, Convex ℝ (C k))
    (hCm : ∀ k, MeasurableSet (C k)) (hCfin : ∀ k, volume (C k) ≠ ⊤)
    (hCpos : ∀ k, 0 < volume (C k)) (hsfin : ∀ k, ∀ t : ℝ, volume (slice (C k) t) ≠ ⊤)
    (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (0:ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Ioo (0:ℝ) 1, (slice (C k) t).Nonempty)
    {B : ℝ} (hB : ∀ k, ∀ t : ℝ, (volume (slice (C k) t)).toReal / (volume (C k)).toReal ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ W : ℝ → ℝ, ∀ t : ℝ,
      Tendsto (fun k => (volume (slice (C (φ k)) t)).toReal / (volume (C (φ k))).toReal)
        atTop (𝓝 (W t)) := by
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hminv : (0:ℝ) < 1 / (m : ℝ) := by positivity
  have hVpos : ∀ k, 0 < (volume (C k)).toReal := fun k =>
    ENNReal.toReal_pos (hCpos k).ne' (hCfin k)
  have hp0 : ∀ (k : ℕ) (t : ℝ),
      0 ≤ (volume (slice (C k) t)).toReal / (volume (C k)).toReal :=
    fun k t => div_nonneg ENNReal.toReal_nonneg (hVpos k).le
  -- the profile vanishes off the slab
  have hpoff : ∀ (k : ℕ) (t : ℝ), t ∉ Icc (0:ℝ) 1 →
      (volume (slice (C k) t)).toReal / (volume (C k)).toReal = 0 := by
    intro k t ht
    have hempty : slice (C k) t = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy => ht (by simpa using hslab k _ hy)
    rw [hempty, measure_empty]
    simp
  have hconc : ∀ k : ℕ, ConcaveOn ℝ (Ioo (0:ℝ) 1)
      (fun t => ((volume (slice (C k) t)).toReal / (volume (C k)).toReal) ^ (1 / (m : ℝ))) := by
    intro k
    have hbase := brunn_slice_concaveOn hm (hconv k) (hCm k) (convex_Ioo (0:ℝ) 1)
      (hspan k) (fun t _ => hsfin k t)
    have hsm := hbase.smul (c := ((volume (C k)).toReal ^ (1 / (m : ℝ)))⁻¹) (by positivity)
    have heq : (fun t => ((volume (slice (C k) t)).toReal / (volume (C k)).toReal) ^ (1 / (m:ℝ)))
        = fun t => ((volume (C k)).toReal ^ (1 / (m : ℝ)))⁻¹
            • ((volume (slice (C k) t)).toReal ^ (1 / (m : ℝ))) := by
      funext t
      rw [Real.div_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg, smul_eq_mul,
        div_eq_inv_mul]
    rw [heq]
    exact hsm
  have hu0 : ∀ (k : ℕ) (t : ℝ),
      0 ≤ ((volume (slice (C k) t)).toReal / (volume (C k)).toReal) ^ (1 / (m : ℝ)) :=
    fun k t => Real.rpow_nonneg (hp0 k t) _
  have huM : ∀ (k : ℕ) (t : ℝ),
      ((volume (slice (C k) t)).toReal / (volume (C k)).toReal) ^ (1 / (m : ℝ))
        ≤ B ^ (1 / (m : ℝ)) :=
    fun k t => Real.rpow_le_rpow (hp0 k t) (hB k t) hminv.le
  have hoff : ∀ (k : ℕ), ∀ t : ℝ, t ∉ Icc (0:ℝ) 1 →
      ((volume (slice (C k) t)).toReal / (volume (C k)).toReal) ^ (1 / (m : ℝ)) = 0 := by
    intro k t ht
    rw [hpoff k t ht, Real.zero_rpow hminv.ne']
  obtain ⟨φ, hφ, V, hV⟩ := exists_subseq_tendsto_of_concaveOn_Ioo hconc hu0 huM hoff
  refine ⟨φ, hφ, fun t => V t ^ m, fun t => ?_⟩
  have hpow := (hV t).pow m
  have heq : ∀ k : ℕ,
      (((volume (slice (C k) t)).toReal / (volume (C k)).toReal) ^ (1 / (m : ℝ))) ^ m
        = (volume (slice (C k) t)).toReal / (volume (C k)).toReal := by
    intro k
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (hp0 k t) hm
  simpa only [heq] using hpow

/-- **(G2b), proved: the normalised slice profile of a convex body in the unit slab is bounded
by `2^(m+1)`, uniformly over all such bodies.**

For a convex measurable `C` in the slab `{x | x 0 ∈ [0,1]}` of finite positive volume, whose
slices are nonempty and of finite volume at *every* height in `[0,1]`,

`vol (slice C t) ≤ 2^(m+1) · vol C`   for every `t : ℝ`.

The proof: the `1/m`-th root profile `u` is concave (`Arlib.brunn_slice_concaveOn`), so by
`Arlib.half_le_of_concaveOn_Icc` it is `≥ u t / 2` on `[t/2, (1+t)/2]`, an interval of length
`1/2` regardless of `t`.  Integrating `u^m` over that interval and comparing with
`Arlib.integral_volume_slice` (`∫ u^m = vol C`) gives `(u t/2)^m/2 ≤ vol C`.

Note that the profile is *integrable* automatically: it is nonnegative with
`∫ = vol C > 0`, so it cannot be non-integrable (which would force `∫ = 0`). -/
theorem normalised_volume_slice_le (hm : m ≠ 0) {C : Set (Fin (m + 1) → ℝ)}
    (hconv : Convex ℝ C) (hCm : MeasurableSet C) (hCfin : volume C ≠ ⊤)
    (hCpos : 0 < volume C) (hsfin : ∀ t : ℝ, volume (slice C t) ≠ ⊤)
    (hslab : ∀ x ∈ C, x 0 ∈ Icc (0:ℝ) 1)
    (hspan : ∀ t ∈ Icc (0:ℝ) 1, (slice C t).Nonempty) (t : ℝ) :
    (volume (slice C t)).toReal / (volume C).toReal ≤ 2 ^ (m + 1) := by
  have hVpos : (0:ℝ) < (volume C).toReal := ENNReal.toReal_pos hCpos.ne' hCfin
  have hF0 : ∀ r : ℝ, (0:ℝ) ≤ (volume (slice C r)).toReal := fun _ => ENNReal.toReal_nonneg
  have hFint0 : ∫ r : ℝ, (volume (slice C r)).toReal = (volume C).toReal :=
    integral_volume_slice hCm hCfin
  have hFint : Integrable (fun r : ℝ => (volume (slice C r)).toReal) := by
    by_contra hcon
    rw [integral_undef hcon] at hFint0
    exact hVpos.ne hFint0
  by_cases ht : t ∈ Icc (0:ℝ) 1
  swap
  · have hempty : slice C t = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy => ht (by simpa using hslab _ hy)
    rw [hempty, measure_empty, ENNReal.toReal_zero, zero_div]
    positivity
  have huc : ConcaveOn ℝ (Icc (0:ℝ) 1)
      (fun r => (volume (slice C r)).toReal ^ (1 / (m : ℝ))) :=
    brunn_slice_concaveOn hm hconv hCm (convex_Icc 0 1) hspan (fun r _ => hsfin r)
  have hu0 : ∀ r : ℝ, (0:ℝ) ≤ (volume (slice C r)).toReal ^ (1 / (m : ℝ)) :=
    fun r => Real.rpow_nonneg (hF0 r) _
  have hum : ∀ r : ℝ,
      ((volume (slice C r)).toReal ^ (1 / (m : ℝ))) ^ m = (volume (slice C r)).toReal := by
    intro r; rw [one_div]; exact Real.rpow_inv_natCast_pow (hF0 r) hm
  have hlowF : ∀ r ∈ Icc (t / 2) ((1 + t) / 2),
      (((volume (slice C t)).toReal ^ (1 / (m : ℝ))) / 2) ^ m ≤ (volume (slice C r)).toReal := by
    intro r hr
    rw [← hum r]
    have hhalf := half_le_of_concaveOn_Icc huc (fun x _ => hu0 x) ht hr.1 hr.2
    have h0 : (0:ℝ) ≤ ((volume (slice C t)).toReal ^ (1 / (m : ℝ))) / 2 := by positivity
    gcongr
  have hJvol : (volume (Icc (t / 2) ((1 + t) / 2))).toReal = 1 / 2 := by
    rw [Real.volume_Icc, show (1 + t) / 2 - t / 2 = 1 / 2 by ring]
    norm_num
  have hJtop : volume (Icc (t / 2) ((1 + t) / 2)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hkey : (((volume (slice C t)).toReal ^ (1 / (m : ℝ))) / 2) ^ m * (1 / 2)
      ≤ (volume C).toReal := by
    calc (((volume (slice C t)).toReal ^ (1 / (m : ℝ))) / 2) ^ m * (1 / 2)
        = (((volume (slice C t)).toReal ^ (1 / (m : ℝ))) / 2) ^ m
            * (volume (Icc (t / 2) ((1 + t) / 2))).toReal := by rw [hJvol]
      _ ≤ ∫ r in Icc (t / 2) ((1 + t) / 2), (volume (slice C r)).toReal := by
            have h := setIntegral_ge_of_const_le_real (μ := (volume : Measure ℝ))
              (s := Icc (t / 2) ((1 + t) / 2)) measurableSet_Icc hJtop hlowF
              hFint.integrableOn
            simpa [Measure.real] using h
      _ ≤ ∫ r : ℝ, (volume (slice C r)).toReal :=
            setIntegral_le_integral hFint (Eventually.of_forall hF0)
      _ = (volume C).toReal := hFint0
  have hrw : (((volume (slice C t)).toReal ^ (1 / (m : ℝ))) / 2) ^ m * (1 / 2)
      = ((volume (slice C t)).toReal ^ (1 / (m : ℝ))) ^ m / 2 ^ (m + 1) := by
    rw [div_pow, pow_succ]; ring
  rw [hrw, div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ (m + 1)), hum t] at hkey
  rw [div_le_iff₀ hVpos]
  linarith

/-- **A bounded measurable function supported in `[0,1]` is integrable.**

This is the shape in which the localisation profiles come out: nonnegative, bounded above by
`2^(m+1)` (`Arlib.normalised_volume_slice_le`, `Arlib.rescaledProfile_le`), and vanishing off the
unit slab.  It is stated separately because it is needed at both origins of the existential `W` —
`Arlib.exists_needleIntegral_eq_zero_and_pos` and
`Arlib.exists_needleIntegral_eq_zero_and_pos_shrinkingSlab`.

Integrability is not decorative: a Bochner integral of a *non*-integrable nonnegative function is
`0`, not `+∞`, so any downstream monotone comparison of needle masses is false without it. -/
theorem integrable_of_forall_notMem_Icc {W : ℝ → ℝ} {B : ℝ} (hWm : Measurable W)
    (hW0 : ∀ t, 0 ≤ W t) (hWB : ∀ t, W t ≤ B)
    (hWsupp : ∀ t : ℝ, t ∉ Icc (0 : ℝ) 1 → W t = 0) :
    Integrable W := by
  have hdom : Integrable (Set.indicator (Icc (0 : ℝ) 1) (fun _ => B)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  refine hdom.mono' hWm.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht, Real.norm_eq_abs, abs_of_nonneg (hW0 t)]
    exact hWB t
  · rw [Set.indicator_of_notMem ht, hWsupp t ht, norm_zero]

/-- **(G2a) and (G2b) together: selection with the uniform bound discharged.**

Same as `Arlib.exists_subseq_tendsto_normalised_slice_profile`, but with no `B` hypothesis: the
uniform bound `2^(m+1)` is supplied by `Arlib.normalised_volume_slice_le`.  The price is that
the slices must be nonempty at *every* height of the closed interval `[0,1]`, not just the
open one. -/
theorem exists_subseq_tendsto_normalised_slice_profile' (hm : m ≠ 0)
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hconv : ∀ k, Convex ℝ (C k))
    (hCm : ∀ k, MeasurableSet (C k)) (hCfin : ∀ k, volume (C k) ≠ ⊤)
    (hCpos : ∀ k, 0 < volume (C k)) (hsfin : ∀ k, ∀ t : ℝ, volume (slice (C k) t) ≠ ⊤)
    (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (0:ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0:ℝ) 1, (slice (C k) t).Nonempty) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ W : ℝ → ℝ, ∀ t : ℝ,
      Tendsto (fun k => (volume (slice (C (φ k)) t)).toReal / (volume (C (φ k))).toReal)
        atTop (𝓝 (W t)) :=
  exists_subseq_tendsto_normalised_slice_profile hm hconv hCm hCfin hCpos hsfin hslab
    (fun k t ht => hspan k t (Ioo_subset_Icc_self ht))
    (B := 2 ^ (m + 1))
    (fun k t => normalised_volume_slice_le hm (hconv k) (hCm k) (hCfin k) (hCpos k)
      (hsfin k) (hslab k) (hspan k) t)

/-- **(G2a) discharged into its consumer.**

Combining `Arlib.exists_subseq_tendsto_normalised_slice_profile` with
`Arlib.tendsto_average_setIntegral_of_profile`: under the hypotheses of the latter *minus* the
undischarged profile-convergence hypothesis `hlim`, and with the bodies convex, spanning and
slice-finite, there is a **subsequence** along which the normalised integrals of `f` converge to
a needle integral.

This is the localisation limit passage with (G2a) removed from the hypothesis list. -/
theorem exists_subseq_tendsto_average_setIntegral (hm : m ≠ 0)
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hconv : ∀ k, Convex ℝ (C k))
    (hCm : ∀ k, MeasurableSet (C k)) (hCfin : ∀ k, volume (C k) ≠ ⊤)
    (hCpos : ∀ k, 0 < volume (C k)) (hsfin : ∀ k, ∀ t : ℝ, volume (slice (C k) t) ≠ ⊤)
    (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (0:ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Ioo (0:ℝ) 1, (slice (C k) t).Nonempty)
    {f : (Fin (m + 1) → ℝ) → ℝ} (hfm : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    {δ : ℕ → ℝ} (hδ : ∀ k, ∀ x ∈ C k, |f x - f (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0)) {B : ℝ}
    (hB : ∀ k, ∀ t : ℝ, (volume (slice (C k) t)).toReal / (volume (C k)).toReal ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ W : ℝ → ℝ,
      Tendsto (fun k => (∫ x in C (φ k), f x) / (volume (C (φ k))).toReal) atTop
        (𝓝 (∫ t : ℝ, W t * f (Fin.cons t (0 : Fin m → ℝ)))) := by
  obtain ⟨φ, hφ, W, hW⟩ := exists_subseq_tendsto_normalised_slice_profile hm hconv hCm hCfin
    hCpos hsfin hslab hspan hB
  refine ⟨φ, hφ, W, ?_⟩
  exact tendsto_average_setIntegral_of_profile (C := fun k => C (φ k)) (fun k => hCm (φ k))
    (fun k => hCfin (φ k)) (fun k => hCpos (φ k)) (fun k => hslab (φ k)) hfm hM
    (δ := fun k => δ (φ k)) (fun k => hδ (φ k)) (hδ0.comp hφ.tendsto_atTop)
    (B := B) (fun k => hB (φ k)) hW

/-- **(G2a) and (G2b) both discharged into the consumer.**

`Arlib.tendsto_average_setIntegral_of_profile` with *both* of its undischarged profile
hypotheses removed.  What remains is exactly: the bodies are convex, measurable, of finite
positive volume, sit in and span the unit slab with slices of finite volume; `f` is bounded
measurable; and the transverse-thinness moduli `δ k` tend to `0` — the interface with (G1). -/
theorem exists_subseq_tendsto_average_setIntegral' (hm : m ≠ 0)
    {C : ℕ → Set (Fin (m + 1) → ℝ)} (hconv : ∀ k, Convex ℝ (C k))
    (hCm : ∀ k, MeasurableSet (C k)) (hCfin : ∀ k, volume (C k) ≠ ⊤)
    (hCpos : ∀ k, 0 < volume (C k)) (hsfin : ∀ k, ∀ t : ℝ, volume (slice (C k) t) ≠ ⊤)
    (hslab : ∀ k, ∀ x ∈ C k, x 0 ∈ Icc (0:ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0:ℝ) 1, (slice (C k) t).Nonempty)
    {f : (Fin (m + 1) → ℝ) → ℝ} (hfm : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    {δ : ℕ → ℝ} (hδ : ∀ k, ∀ x ∈ C k, |f x - f (Fin.cons (x 0) (0 : Fin m → ℝ))| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ W : ℝ → ℝ,
      Tendsto (fun k => (∫ x in C (φ k), f x) / (volume (C (φ k))).toReal) atTop
        (𝓝 (∫ t : ℝ, W t * f (Fin.cons t (0 : Fin m → ℝ)))) :=
  exists_subseq_tendsto_average_setIntegral hm hconv hCm hCfin hCpos hsfin hslab
    (fun k t ht => hspan k t (Ioo_subset_Icc_self ht)) hfm hM hδ hδ0
    (B := 2 ^ (m + 1))
    (fun k t => normalised_volume_slice_le hm (hconv k) (hCm k) (hCfin k) (hCpos k)
      (hsfin k) (hslab k) (hspan k) t)

/-! ### Non-vacuity

The theorems above bundle seven or eight hypotheses.  The following witness checks that they
can hold **simultaneously**, with nonzero volumes and a **nonzero** limit profile, so that
nothing above is a statement about an empty configuration. -/

/-- **Non-vacuity of the (G2a)/(G2b) hypothesis bundle.**

The constant sequence `C k = [0,1]^(m+1)` satisfies every hypothesis of
`Arlib.exists_subseq_tendsto_normalised_slice_profile'`, and the limit profile it produces is
nonzero: `W (1/2) = 1`. -/
theorem exists_subseq_tendsto_normalised_slice_profile_unitCube (hm : m ≠ 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ W : ℝ → ℝ,
      (∀ t : ℝ, Tendsto (fun k =>
          (volume (slice ((fun _ : ℕ => Set.univ.pi fun _ : Fin (m + 1) => Icc (0:ℝ) 1) (φ k))
            t)).toReal
          / (volume ((fun _ : ℕ => Set.univ.pi fun _ : Fin (m + 1) => Icc (0:ℝ) 1)
            (φ k))).toReal) atTop (𝓝 (W t)))
        ∧ W (1 / 2) = 1 := by
  set Q : Set (Fin (m + 1) → ℝ) := Set.univ.pi fun _ => Icc (0:ℝ) 1 with hQ
  have hQm : MeasurableSet Q := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hQconv : Convex ℝ Q := convex_pi fun _ _ => convex_Icc 0 1
  have hQvol : volume Q = 1 := by rw [hQ, volume_pi_pi]; simp [Real.volume_Icc]
  have hslice_mem : ∀ t ∈ Icc (0:ℝ) 1,
      slice Q t = Set.univ.pi fun _ : Fin m => Icc (0:ℝ) 1 := by
    intro t ht
    ext y
    simp only [mem_slice, hQ, Set.mem_univ_pi]
    constructor
    · intro h j; simpa using h j.succ
    · intro h i
      refine Fin.cases ?_ ?_ i
      · simpa using ht
      · intro j; simpa using h j
  have hslice_not : ∀ t : ℝ, t ∉ Icc (0:ℝ) 1 → slice Q t = ∅ := by
    intro t ht
    refine Set.eq_empty_of_forall_notMem fun y hy => ht ?_
    have h := (Set.mem_univ_pi.mp (show (Fin.cons t y : Fin (m + 1) → ℝ) ∈ Q from hy)) 0
    simpa using h
  have hsvol : ∀ t ∈ Icc (0:ℝ) 1, volume (slice Q t) = 1 := by
    intro t ht; rw [hslice_mem t ht, volume_pi_pi]; simp [Real.volume_Icc]
  have hsfin : ∀ t : ℝ, volume (slice Q t) ≠ ⊤ := by
    intro t
    by_cases ht : t ∈ Icc (0:ℝ) 1
    · rw [hsvol t ht]; exact ENNReal.one_ne_top
    · rw [hslice_not t ht, measure_empty]; exact ENNReal.zero_ne_top
  have hspan : ∀ t ∈ Icc (0:ℝ) 1, (slice Q t).Nonempty := by
    intro t ht
    rw [hslice_mem t ht]
    exact ⟨0, Set.mem_univ_pi.mpr fun _ => ⟨le_refl 0, zero_le_one⟩⟩
  obtain ⟨φ, hφ, W, hW⟩ := exists_subseq_tendsto_normalised_slice_profile' hm
    (C := fun _ => Q) (fun _ => hQconv) (fun _ => hQm)
    (fun _ => by rw [hQvol]; exact ENNReal.one_ne_top)
    (fun _ => by rw [hQvol]; exact zero_lt_one) (fun _ => hsfin)
    (fun _ x hx => Set.mem_univ_pi.mp hx 0) (fun _ => hspan)
  refine ⟨φ, hφ, W, hW, ?_⟩
  have hconst : (fun k : ℕ => (volume (slice Q (1/2 : ℝ))).toReal / (volume Q).toReal)
      = fun _ : ℕ => (1:ℝ) := by
    funext k
    rw [hsvol (1/2 : ℝ) ⟨by norm_num, by norm_num⟩, hQvol]
    norm_num
  have h1 := hW (1/2 : ℝ)
  rw [hconst] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

end SliceProfile

end Arlib

#print axioms Arlib.volume_slice_ne_top_of_forall_abs_le
#print axioms Arlib.sub_le_of_concaveOn_Ioo_right
#print axioms Arlib.sub_le_of_concaveOn_Ioo_left
#print axioms Arlib.abs_sub_le_of_concaveOn_Ioo
#print axioms Arlib.half_le_of_concaveOn_Icc
#print axioms Arlib.exists_subseq_tendsto_of_concaveOn_Ioo
#print axioms Arlib.exists_subseq_tendsto_normalised_slice_profile
#print axioms Arlib.normalised_volume_slice_le
#print axioms Arlib.integrable_of_forall_notMem_Icc
#print axioms Arlib.exists_subseq_tendsto_normalised_slice_profile'
#print axioms Arlib.exists_subseq_tendsto_average_setIntegral
#print axioms Arlib.exists_subseq_tendsto_average_setIntegral'
#print axioms Arlib.exists_subseq_tendsto_normalised_slice_profile_unitCube
