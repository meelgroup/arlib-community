/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LogisticIso

/-!
# Lovász–Vempala Theorem 2.1: the weighted isoperimetric inequality

> L. Lovász and S. Vempala, *Hit-and-Run from a Corner*, STOC 2004 / SIAM J. Comput. **35**
> (2006) 985–1005, §2.

> **Theorem 2.1.**  Let `K ⊆ ℝⁿ` be a convex body, `f : K → ℝ₊` logconcave and `h : K → ℝ₊`
> arbitrary.  Let `S₁, S₂, S₃` be any partition of `K` into measurable sets.  Suppose that for
> any pair `u ∈ S₁`, `v ∈ S₂` and any point `x` on the chord of `K` through `u` and `v`,
> `h(x) ≤ (1/3)·min{1, d_K(u,v)}`.  Then `∫_{S₃} f ≥ E_f(h)·min{∫_{S₁} f, ∫_{S₂} f}`.

This is the statement that `Arlib/MarkovChains/Continuous/HitAndRunConductance.lean` carries as
the inline hypothesis `hIso` of `Arlib.MarkovChains.conductance_hitAndRun_ge`, and calls "the
whole remaining mathematical distance between this file and an unconditional Theorem 4.2".

## 1. **Theorem 2.1 is false as stated, and so is `hIso`**

The hypothesis constrains `h` **only on the union of the chords through cross pairs**
`(u,v) ∈ S₁ × S₂`.  The conclusion integrates `h` over **all of `K`**.  In dimension `n ≥ 2`
that union can miss a set of positive measure, and on that set `h` is unconstrained, so the
left-hand side can be made arbitrarily large while the right-hand side is bounded by `vol K`.

**Explicit counterexample.**  Take `n = 2`, `K = [0,1]²`, `f ≡ 1` (uniform, logconcave), and

    S₁ = [0, 1/8]²,        S₂ = [7/8, 1] × [0, 1/8],        S₃ = K ∖ S₁ ∖ S₂.

Let `u ∈ S₁`, `v ∈ S₂` and let `x = u + r(v − u)` be a point of `K` on their chord.  Then
`v₀ − u₀ ≥ 3/4` and `|v₁ − u₁| ≤ 1/8`, while `x₀ ∈ [0,1]` forces
`r(v₀ − u₀) = x₀ − u₀ ∈ [−1/8, 1]`, hence `r ∈ [−1/6, 4/3]`; therefore

    x₁ ≤ u₁ + |r|·|v₁ − u₁| ≤ 1/8 + (4/3)(1/8) = 7/24 < 1/3.

So **no cross chord meets `N = K ∩ {x₁ > 1/3}`**, which has measure `2/3`.  Put
`h = M·1_N` for `M > 0`.  Every hypothesis holds — `h ≥ 0`, and on a cross chord `h = 0 ≤
(1/3)min(1, d_K(u,v))` because `d_K ≥ 0` — yet

    E(h)·min{vol S₁, vol S₂} = M·(2/3)·(1/64)  →  ∞     while    vol S₃ = 1 − 2/64 < 1.

Any `M > 96` refutes the conclusion.  `hIso` of `HitAndRunConductance.lean`, *as it stood
before the repair recorded below*, was this statement verbatim for the uniform density, so it
was **a false hypothesis**: dilating the
counterexample by `4` gives `K = [0,4]²` (which contains a unit ball, at centre `(2,2)`),
`D = 4√2`, `S₁ = [0,1/2]²`, `S₂ = [7/2,4]×[0,1/2]`, `N = K ∩ {x₁ > 4/3}` — every *other*
hypothesis of `conductance_hitAndRun_ge` is then satisfiable at `n = 2`, while `hIso` is not.
So the theorem's guarantee is **empty at that instance**, and generically for `n ≥ 2` wherever
the two-box configuration embeds after an affine map.  (It says nothing about `n = 1`, where
every chord is all of `K` and the chord hypothesis does constrain `h` everywhere.)

**Where the paper's proof breaks.**  §2 bounds `M_ab = max{h(x) : x on the chord through a, b}`
by `1/3` using the hypothesis at a cross pair *on the needle*.  The Localization Lemma forces
`∫_{J₁} F = A∫F > 0`, so the needle meets `S₁`; nothing forces it to meet `S₂`.  On a needle
disjoint from `S₂` — exactly the one running from `S₁` through `N` in the counterexample —
there is no cross pair and no bound on `M_ab`, and the final step "`(2)` and `(3)` imply
`M_ab > 1/3`, a contradiction" has nothing to contradict.

**The repair, which costs nothing.**  Add the *global* bound

    ∀ x ∈ K,  h x ≤ 1/3

as a hypothesis.  It is exactly what the paper's own application of Theorem 2.1 verifies —
"Clearly `h(x) ≤ 1/3`" (§4), proved in this repository as
`Arlib.MarkovChains.stepRadius_le_two_mul_diam`, which gives `h ≤ 1/(24√n) ≤ 1/3` — so no
downstream consumer loses anything.  With it, `M ≤ 1/3` is available whether or not the needle
meets `S₂`, and the paper's argument goes through unchanged; that is `Arlib.needle_iso` below.

**The repair, as applied.**  `HitAndRunConductance.lean` now carries exactly **one** extra
clause in `hIso` (and `HitAndRunMixing.lean` threads the same clause through both of its
capstones):

    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂))

It is discharged at the use site by `Arlib.MarkovChains.weight_le_third`, which gives the
stronger `h ≤ 1/(24√n)` — the paper's own "clearly `h(x) ≤ 1/3`" — so no caller supplies it.

**`Measurable h` was deliberately *not* added.**  An earlier draft of this docstring proposed it
as a second insertion, on the grounds that a `∫⁻` has to become a Bochner integral somewhere.
Two facts say otherwise.  (i) It is not part of the repair: `Arlib.not_hIso_two_measurable`
refutes the old binder even when restricted to measurable `h`, since the counterexample weight
is an indicator.  (ii) The consumer cannot discharge it: there is no measurability lemma for
`Arlib.stepRadius` anywhere in this repository, so the clause would be an obligation nobody can
meet.  Nor does omitting it make `hIso` materially harder to prove — Mathlib's `∫⁻` is a
supremum over simple functions below `h`, and each of those inherits both the chord bound and
the `1/3` bound, so the arbitrary-`h` case reduces to the measurable one.  Whoever eventually
finds they need measurability must land `Measurable (Arlib.stepRadius K α)` in the same
change.

## 2. Borsuk–Ulam is **not** needed — the old `HitAndRunConductance.lean` claim was stale

An earlier revision of that docstring (at what were then lines 50–53; the text has since been
corrected in place) said the signed case of the transverse cut "is where Borsuk–Ulam re-enters",
and that Borsuk–Ulam is absent from Mathlib, hence `hIso` is out of reach.  This is not true,
and the file that supersedes it says so explicitly
(`Arlib/Convexity/LocalizationAssembly.lean:42–44`: *"no Borsuk–Ulam is used: with the equality
form, only one integrand ever needs bisecting"*).  Checked at the declaration, not the prose:
`Arlib.exists_flat_cut_zero_pos` (`LocalizationAssembly.lean:370`) takes **arbitrary signed**
`g₁ g₂ : E → ℝ` — its only hypotheses on them are `IntegrableOn`, `∫_C g₁ = 0`, `0 < ∫_C g₂` —
and produces a cut with `∫ g₁ = 0` and `0 < ∫ g₂` on one side.  The equality form bisects `g₁`
alone (a one-parameter intermediate value theorem, `Arlib.exists_pencil_bisecting`), and `g₂`
needs no bisection because its two masses sum to something positive.  So the residual obstacle
to `hIso` is **not** Borsuk–Ulam; it is the two hypotheses that
`Arlib/Convexity/LocalizationAssembly.lean` classifies as genuinely open — **(C)** lower
semicontinuity (the needle theorems ask for *continuous* integrands, and `1_{T₁}` is not) and
**(F)** the measure-preserving transport `EuclideanSpace ℝ (Fin n) ≃ (Fin (m+1) → ℝ)` plus
nondegeneracy of the limit body.

## 3. What is proved here

Everything in §2 of the paper except the Localization Lemma itself.

* `Arlib.isLogConcave_indicator_of_logConcaveOn` — truncating a log-concave function to its
  convex domain keeps it log-concave, so results stated for globally log-concave weights apply
  to a needle profile that is log-concave only on `[α, β]`.
* `Arlib.crossRatioIcc_mul_le` — **the interval case**: for `α ≤ x ≤ y ≤ β`, the cross-ratio
  coefficient `(β−α)(y−x)/((x−α)(β−y))` of the segment `[α,β]` is an isoperimetric coefficient
  for any log-concave weight.  This is `Arlib.crossRatio_mul_le_crossRatio_integral`
  (Lovász–Vempala Lemma 5.9) divided through, with all three degenerate positions handled.
* `Arlib.oneDim_crossRatio_partition` — **the one-dimensional case of the paper's inequality
  `(1)`**, for an arbitrary measurable three-way partition, via `Arlib.oneDim_partition`.
* `Arlib.needle_iso` — **the one-dimensional Theorem 2.1**: the displayed chain of §2, repaired
  as in §1 above.  Nothing is assumed; in particular the argument no longer needs the needle to
  meet `S₂`.
* `Arlib.crossRatioDist_mul_le_of_lineMap_mem` — `d_K(u,v) ≤ d_S(u,v)` for a sub-segment
  `S ⊆ K` of the chord containing `u, v`, division-free.  The paper uses this silently when it
  compares `d_K(ua+(1−u)b, va+(1−v)b)` with `(v−u)/(u(1−v))`; the printed inequality signs there
  are unreadable in the available scan, and this is the direction that makes the proof work.
* `Arlib.needle_crossRatio_transfer`, `Arlib.three_mul_sSup_le_crossRatioDist` — the two steps
  that carry the ambient hypothesis onto a needle.
* `Arlib.needle_iso_of_chord` — **Theorem 2.1 on a needle inside `K`**, from the ambient
  hypotheses.  This is the whole of §2 apart from the localisation step, and it is
  unconditional.
* `Arlib.thm21_of_localization` — **Theorem 2.1 for the uniform density**, with the Localization
  Lemma as its single binder `hloc`.
* `Arlib.chord_le_of_corner_boxes` — **the geometric core of the counterexample of §1**, proved:
  no chord of `[0,1]²` through `[0,1/8]²` and `[7/8,1]×[0,1/8]` ever reaches height `7/24`, let
  alone `1/3`.

**The counterexample of §1 is machine-checked end to end** in
`Arlib.Convexity.LovaszVempalaIsoFalse`: `Arlib.not_hIso_two` is the *negation* of the `hIso`
binder written out verbatim at `n = 2` and `K = [0,4]²`, and `Arlib.cexK_hitAndRun_hypotheses`
discharges every other geometric hypothesis of `conductance_hitAndRun_ge` at that same body.
Nothing in §1 rests on prose any more.

## 4. What is assumed

Exactly one thing: the binder `hloc` of `Arlib.thm21_of_localization`, written out inline at its
declaration.  It is Corollary 2.4 of Kannan–Lovász–Simonovits 1995 applied to
`g₁ = 1_{T₁} − A·1_K` and `g₂ = A·h·1_K − 1_{K∖T₁∖T₂}`, in the same shape as the `hloc` of
`Arlib.gaussianRestricted_isoperimetry`.  Nothing in this file is a `def`, `structure`, `class`
or named `Prop` asserting a conclusion it does not prove.

Note that `Arlib.needle_iso_of_chord` — everything except that one application — is
**unconditional**, and that is where all the mathematics of §2 lives.
-/

namespace Arlib

open MeasureTheory Set

/-! ### Log-concavity of a truncation -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Truncating a log-concave function to its (convex) domain keeps it log-concave.**

If `f` is log-concave on the convex set `s` and nonnegative there, then `s.indicator f` is
log-concave on all of `E`.  This is what lets a statement proved for *globally* log-concave
weights be applied to a needle profile that is only log-concave on `[0,1]`. -/
theorem isLogConcave_indicator_of_logConcaveOn {s : Set E} {f : E → ℝ}
    (hf : LogConcaveOn s f) (hf0 : ∀ x ∈ s, 0 ≤ f x) :
    IsLogConcave (Set.indicator s f) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hnn : ∀ z, 0 ≤ Set.indicator s f z := fun z => Set.indicator_nonneg hf0 z
  by_cases hx : x ∈ s
  · by_cases hy : y ∈ s
    · have hz : a • x + b • y ∈ s := hf.convex hx hy ha hb hab
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
      exact hf.geom_le hx hy ha hb hab
    · rcases eq_or_ne b 0 with rfl | hb'
      · have ha1 : a = 1 := by linarith
        subst ha1
        simp
      · rw [Set.indicator_of_notMem hy, Real.zero_rpow hb', mul_zero]
        exact hnn _
  · rcases eq_or_ne a 0 with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1
      simp
    · rw [Set.indicator_of_notMem hx, Real.zero_rpow ha', zero_mul]
      exact hnn _

/-! ### Two null-set conveniences -/

section NullSets

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}

/-- Removing a null set does not change a set up to `μ`-a.e. equality. -/
theorem ae_eq_sdiff_null {s t : Set X} (ht : μ t = 0) : (s \ t : Set X) =ᵐ[μ] s := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨measure_mono_null (fun x hx => ?_) ht, measure_mono_null (fun x hx => ?_) ht⟩
  · exact absurd hx.1.1 hx.2
  · by_contra hxt
    exact hx.2 ⟨hx.1, hxt⟩

/-- Adjoining a null set does not change a set up to `μ`-a.e. equality. -/
theorem ae_eq_union_null {s t : Set X} (ht : μ t = 0) : (s ∪ t : Set X) =ᵐ[μ] s := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨measure_mono_null (fun x hx => ?_) ht, measure_mono_null (fun x hx => ?_) ht⟩
  · rcases hx.1 with h | h
    exacts [absurd h hx.2, h]
  · exact absurd (Or.inl hx.1) hx.2

end NullSets

/-! ### The interval case of the one-dimensional cross-ratio inequality -/

section OneDim

variable {D : ℝ → ℝ} {α β : ℝ}

/-- Interval integrals inside `[α, β]` do not see the truncation of the integrand to `[α, β]`. -/
theorem intervalIntegral_indicator_Icc {u v : ℝ} (hu : α ≤ u) (huv : u ≤ v) (hv : v ≤ β) :
    (∫ t in u..v, Set.indicator (Set.Icc α β) D t) = ∫ t in u..v, D t := by
  refine intervalIntegral.integral_congr ?_
  intro t ht
  rw [Set.uIcc_of_le huv] at ht
  have htmem : t ∈ Set.Icc α β := ⟨hu.trans ht.1, ht.2.trans hv⟩
  exact Set.indicator_of_mem htmem D

/-- **The interval case: the cross-ratio coefficient of `[α,β]` is an isoperimetric
coefficient for any log-concave weight.**

For `α ≤ x ≤ y ≤ β` and `D` log-concave and nonnegative on `[α, β]`,

    d(x,y) · (∫_α^x D)(∫_y^β D)  ≤  (∫_α^β D)(∫_x^y D),   d(x,y) = (β−α)(y−x)/((x−α)(β−y)),

`d(x,y)` being the cross-ratio distance of `x, y` in the segment `[α, β]`
(`Arlib.crossRatioDist_Icc`).  This is Lovász–Vempala Lemma 5.9
(`Arlib.crossRatio_mul_le_crossRatio_integral`) divided through by `(x−α)(β−y)`, with the
three degenerate positions `x = α`, `x = y`, `y = β` — where Lean's `_ / 0 = 0` makes the
left-hand side vanish anyway — handled separately. -/
theorem crossRatioIcc_mul_le (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t)
    (hlc : LogConcaveOn (Set.Icc α β) D) (hDint : IntervalIntegrable D volume α β)
    {x y : ℝ} (hx : α ≤ x) (hxy : x ≤ y) (hy : y ≤ β) :
    (β - α) * (y - x) / ((x - α) * (β - y)) * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
      ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t := by
  have hαβ : α ≤ β := hx.trans (hxy.trans hy)
  have hRHS : ∀ u v : ℝ, α ≤ u → u ≤ v → v ≤ β →
      0 ≤ (∫ t in α..β, D t) * ∫ t in u..v, D t := by
    intro u v hu huv hv
    exact mul_nonneg (intervalIntegral.integral_nonneg hαβ fun t ht => hD0 t ht)
      (intervalIntegral.integral_nonneg huv fun t ht => hD0 t ⟨hu.trans ht.1, ht.2.trans hv⟩)
  rcases eq_or_lt_of_le hx with h1 | h1
  · rw [← h1, intervalIntegral.integral_same, zero_mul, mul_zero]
    exact hRHS α y le_rfl (h1 ▸ hxy) hy
  rcases eq_or_lt_of_le hxy with h2 | h2
  · rw [← h2, sub_self, mul_zero, zero_div, zero_mul]
    exact hRHS x x hx le_rfl (hxy.trans hy)
  rcases eq_or_lt_of_le hy with h3 | h3
  · rw [h3, intervalIntegral.integral_same, mul_zero, mul_zero]
    exact hRHS x β hx (h3 ▸ hxy) le_rfl
  -- the nondegenerate case: `α < x < y < β`
  set Dc : ℝ → ℝ := Set.indicator (Set.Icc α β) D with hDcdef
  have hDc0 : ∀ t, 0 ≤ Dc t := fun t => Set.indicator_nonneg hD0 t
  have hDclc : IsLogConcave Dc := isLogConcave_indicator_of_logConcaveOn hlc hD0
  have hDcint : IntervalIntegrable Dc volume α β := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hαβ] at hDint ⊢
    exact hDint.congr_fun (fun t ht => (Set.indicator_of_mem ht D).symm) measurableSet_Icc
  have hmain := crossRatio_mul_le_crossRatio_integral hDc0 hDclc h1 h2 h3 hDcint
  rw [intervalIntegral_indicator_Icc le_rfl hx (hxy.trans hy),
    intervalIntegral_indicator_Icc hx hxy hy,
    intervalIntegral_indicator_Icc (hx.trans hxy) hy le_rfl,
    intervalIntegral_indicator_Icc le_rfl hαβ le_rfl] at hmain
  have hden : (0 : ℝ) < (x - α) * (β - y) := mul_pos (by linarith) (by linarith)
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [hmain]

/-- **The one-dimensional case of Lovász–Vempala's inequality (1), for an arbitrary measurable
three-way partition.**

Let `D ≥ 0` be log-concave on `[α, β]` and let `Z₁, Z₂, Z₃` partition `[α, β]` into measurable
sets such that every *cross pair* `s ∈ Z₁`, `t ∈ Z₂` is at cross-ratio distance at least `c`
inside the segment `[α, β]`.  Then

    c · (∫_{Z₁} D)(∫_{Z₂} D)  ≤  (∫_α^β D)(∫_{Z₃} D).

This is the statement Lovász–Vempala quote as `(1)` (Theorem 2.5 of Lovász–Vempala,
*The geometry of logconcave functions and sampling algorithms*) in the one dimension in which
their proof of Theorem 2.1 uses it.

**The separation hypothesis is stated division-free** — `c·(min−α)(β−max) ≤ (β−α)(max−min)`
rather than `c ≤ (β−α)(max−min)/((min−α)(β−max))` — so that it is satisfiable, rather than
false, at a cross pair sitting at an endpoint of `[α, β]`, where the quotient is `∞` and Lean's
junk value for it is `0`.  The endpoints are moved into `Z₃` inside the proof; they carry no
mass, and after the move every cross pair is interior and the quotient form is available.

The interval case is `Arlib.crossRatioIcc_mul_le`, and the passage from it to a measurable
partition is `Arlib.oneDim_partition`, used verbatim. -/
theorem oneDim_crossRatio_partition {D : ℝ → ℝ} {α β c : ℝ} (hαβ : α ≤ β)
    (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hlc : LogConcaveOn (Set.Icc α β) D)
    (hDint : IntervalIntegrable D volume α β)
    {Z₁ Z₂ Z₃ : Set ℝ} (hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃)
    (hm₁ : MeasurableSet Z₁) (hm₂ : MeasurableSet Z₂) (hm₃ : MeasurableSet Z₃)
    (hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂,
      c * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t)) :
    c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t) ≤ (∫ t in α..β, D t) * ∫ t in Z₃, D t := by
  classical
  set P : Set ℝ := {α, β} with hPdef
  have hPfin : P.Finite := (Set.finite_singleton β).insert α
  have hPnull : volume P = 0 := hPfin.measure_zero volume
  have hPmeas : MeasurableSet P := hPfin.measurableSet
  have hPsub : P ⊆ Set.Icc α β := by
    intro t ht
    simp only [hPdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    exacts [⟨le_rfl, hαβ⟩, ⟨hαβ, le_rfl⟩]
  -- the endpoints, which carry no mass, are moved into the third part
  have hpart' : IsPartition3 (Set.Icc α β) (Z₁ \ P) (Z₂ \ P) (Z₃ ∪ P) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine Set.Subset.antisymm ?_ ?_
      · rintro x ((⟨h, -⟩ | ⟨h, -⟩) | (h | h))
        exacts [hpart.subset₁ h, hpart.subset₂ h, hpart.subset₃ h, hPsub h]
      · intro x hx
        have hx3 : x ∈ Z₁ ∪ Z₂ ∪ Z₃ := by rw [hpart.union]; exact hx
        by_cases hxP : x ∈ P
        · exact Or.inr (Or.inr hxP)
        · rcases hx3 with (h | h) | h
          exacts [Or.inl (Or.inl ⟨h, hxP⟩), Or.inl (Or.inr ⟨h, hxP⟩), Or.inr (Or.inl h)]
    · exact hpart.disjoint₁₂.mono Set.diff_subset Set.diff_subset
    · rw [Set.disjoint_union_right]
      exact ⟨hpart.disjoint₁₃.mono Set.diff_subset le_rfl, Set.disjoint_sdiff_left⟩
    · rw [Set.disjoint_union_right]
      exact ⟨hpart.disjoint₂₃.mono Set.diff_subset le_rfl, Set.disjoint_sdiff_left⟩
  -- the separation hypothesis in quotient form, now that every cross pair is interior
  have hcross' : ∀ s ∈ Z₁ \ P, ∀ t ∈ Z₂ \ P,
      c ≤ (β - α) * (max s t - min s t) / ((min s t - α) * (β - max s t)) := by
    rintro s ⟨hs₁, hsP⟩ t ⟨ht₂, htP⟩
    have hsmem : s ∈ Set.Icc α β := hpart.subset₁ hs₁
    have htmem : t ∈ Set.Icc α β := hpart.subset₂ ht₂
    simp only [hPdef, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hsP htP
    have hsα : α < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsP.1)
    have hsβ : s < β := lt_of_le_of_ne hsmem.2 hsP.2
    have htα : α < t := lt_of_le_of_ne htmem.1 (Ne.symm htP.1)
    have htβ : t < β := lt_of_le_of_ne htmem.2 htP.2
    have hminα : α < min s t := lt_min hsα htα
    have hmaxβ : max s t < β := max_lt hsβ htβ
    have hden : (0 : ℝ) < (min s t - α) * (β - max s t) :=
      mul_pos (by linarith) (by linarith)
    rw [le_div_iff₀ hden]
    exact hcross s hs₁ t ht₂
  have key := oneDim_partition D (Z₁ \ P) (Z₂ \ P) (Z₃ ∪ P)
    (fun x y => (β - α) * (y - x) / ((x - α) * (β - y))) α β c hαβ hD0 hDint hpart'
    (hm₁.diff hPmeas) (hm₂.diff hPmeas) (hm₃.union hPmeas)
    (fun x y hx hxy hy => crossRatioIcc_mul_le hD0 hlc hDint hx hxy hy) hcross'
  -- the three parts differ from the original ones by a null set
  have hae₁ : (Z₁ \ P : Set ℝ) =ᵐ[volume] Z₁ := ae_eq_sdiff_null hPnull
  have hae₂ : (Z₂ \ P : Set ℝ) =ᵐ[volume] Z₂ := ae_eq_sdiff_null hPnull
  have hae₃ : (Z₃ ∪ P : Set ℝ) =ᵐ[volume] Z₃ := ae_eq_union_null hPnull
  rwa [setIntegral_congr_set hae₁, setIntegral_congr_set hae₂,
    setIntegral_congr_set hae₃] at key

/-- A three-way measurable partition of `[α, β]` splits the interval integral. -/
theorem integral_of_isPartition3 {D : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hDint : IntervalIntegrable D volume α β)
    {Z₁ Z₂ Z₃ : Set ℝ} (hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃)
    (hm₂ : MeasurableSet Z₂) (hm₃ : MeasurableSet Z₃) :
    (∫ t in α..β, D t) = (∫ t in Z₁, D t) + (∫ t in Z₂, D t) + ∫ t in Z₃, D t := by
  have hIcc : IntegrableOn D (Set.Icc α β) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mp hDint
  have hstep : (∫ t in α..β, D t) = ∫ t in Set.Icc α β, D t := by
    rw [intervalIntegral.integral_of_le hαβ]
    exact setIntegral_congr_set Ioc_ae_eq_Icc
  have h12 : Disjoint (Z₁ ∪ Z₂) Z₃ := by
    rw [Set.disjoint_union_left]
    exact ⟨hpart.disjoint₁₃, hpart.disjoint₂₃⟩
  have hi₁ : IntegrableOn D Z₁ volume := hIcc.mono_set hpart.subset₁
  have hi₂ : IntegrableOn D Z₂ volume := hIcc.mono_set hpart.subset₂
  have hi₃ : IntegrableOn D Z₃ volume := hIcc.mono_set hpart.subset₃
  have hi₁₂ : IntegrableOn D (Z₁ ∪ Z₂) volume := hi₁.union hi₂
  rw [hstep, ← hpart.union, setIntegral_union h12 hm₃ hi₁₂ hi₃,
    setIntegral_union hpart.disjoint₁₂ hm₂ hi₁ hi₂]

/-- **Theorem 2.1 of Lovász–Vempala on a needle** — the one-dimensional statement that its
proof reduces to, and the only place where the argument has content.

Let `D ≥ 0` be log-concave on `[α, β]`, let `Z₁, Z₂, Z₃` be a measurable partition of `[α, β]`
carrying `∫_{Z₁} D = A·∫_α^β D` with `0 ≤ A ≤ 1/2`, and let `G ≥ 0` satisfy

* `G ≤ M` on all of `[α, β]`, with `M ≤ 1/3`, and
* `3M ≤ d(s,t)` for every cross pair `s ∈ Z₁`, `t ∈ Z₂` (division-free form).

Then `A·∫_α^β G·D ≤ ∫_{Z₃} D`.

This is exactly the displayed chain of Lovász–Vempala §2, in the contrapositive: from
`∫_{Z₃}D < A∫GD` one gets `∫_{Z₃}D < M·∫_{Z₁}D` and, by `Arlib.oneDim_crossRatio_partition`,
`3∫_{Z₂}D < ∫_α^β D`, whence `∫_{Z₃}D > (1 − 1/2 − 1/3)∫_α^β D`, contradicting `M ≤ 1/3`.

**Where the paper's proof is repaired.**  Lovász–Vempala obtain `M ≤ 1/3` from the hypothesis
`h(x) ≤ (1/3)min(1, d_K(u,v))` *applied to a cross pair on the needle*.  If the needle meets
`S₁` but not `S₂` — which the localisation lemma does not forbid, and which is exactly the
configuration realised by the counterexample in this file's module docstring — there is no such
cross pair and no bound on `M` at all.  Here `M ≤ 1/3` is a hypothesis in its own right, and
the cross condition is used *only* for the coefficient `3M`; the argument then needs nothing
about `Z₂` being nonempty. -/
theorem needle_iso {D G : ℝ → ℝ} {α β A M : ℝ} (hαβ : α ≤ β)
    (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hlc : LogConcaveOn (Set.Icc α β) D)
    (hDint : IntervalIntegrable D volume α β)
    (hGM : ∀ t ∈ Set.Icc α β, G t ≤ M) (hM0 : 0 ≤ M) (hM3 : M ≤ 1 / 3)
    (hGDint : IntervalIntegrable (fun t => G t * D t) volume α β)
    {Z₁ Z₂ Z₃ : Set ℝ} (hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃)
    (hm₁ : MeasurableSet Z₁) (hm₂ : MeasurableSet Z₂) (hm₃ : MeasurableSet Z₃)
    (hA0 : 0 ≤ A) (hA : A ≤ 1 / 2)
    (hmass : (∫ t in Z₁, D t) = A * ∫ t in α..β, D t)
    (hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂,
      3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t)) :
    A * (∫ t in α..β, G t * D t) ≤ ∫ t in Z₃, D t := by
  set T := ∫ t in α..β, D t with hTdef
  set T₁ := ∫ t in Z₁, D t with hT₁def
  set T₂ := ∫ t in Z₂, D t with hT₂def
  set T₃ := ∫ t in Z₃, D t with hT₃def
  have hT0 : 0 ≤ T := intervalIntegral.integral_nonneg hαβ fun t ht => hD0 t ht
  have hT₂0 : 0 ≤ T₂ := setIntegral_nonneg hm₂ fun t ht => hD0 t (hpart.subset₂ ht)
  have hT₃0 : 0 ≤ T₃ := setIntegral_nonneg hm₃ fun t ht => hD0 t (hpart.subset₃ ht)
  have hsum : T = T₁ + T₂ + T₃ := integral_of_isPartition3 hαβ hDint hpart hm₂ hm₃
  -- the average of `G` against `D` is at most `M`
  have hGD : (∫ t in α..β, G t * D t) ≤ M * T := by
    have hmono : (∫ t in α..β, G t * D t) ≤ ∫ t in α..β, M * D t := by
      refine intervalIntegral.integral_mono_on hαβ hGDint (hDint.const_mul M) ?_
      intro t ht
      exact mul_le_mul_of_nonneg_right (hGM t ht) (hD0 t ht)
    rwa [intervalIntegral.integral_const_mul] at hmono
  -- the one-dimensional isoperimetric inequality at the coefficient `3M`
  have hiso : 3 * M * (T₁ * T₂) ≤ T * T₃ :=
    oneDim_crossRatio_partition hαβ hD0 hlc hDint hpart hm₁ hm₂ hm₃ hcross
  by_contra hcon'
  have hcon : T₃ < A * ∫ t in α..β, G t * D t := not_le.mp hcon'
  -- `T > 0`, and hence `A > 0` and `T₁ > 0`
  have hAMT : T₃ < A * (M * T) := lt_of_lt_of_le hcon (by nlinarith)
  have hTpos : 0 < T := by
    rcases hT0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hAMT; nlinarith
  have hApos : 0 < A := by
    rcases hA0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hAMT; nlinarith
  have hMpos : 0 < M := by
    rcases hM0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hAMT; nlinarith
  have hT₁pos : 0 < T₁ := by rw [hmass]; positivity
  -- `3 ∫_{Z₂} D < ∫_α^β D`
  have hkey : 3 * T₂ < T := by
    have h1 : 3 * M * (T₁ * T₂) < M * T₁ * T := by nlinarith
    have h2 : 0 < M * T₁ := mul_pos hMpos hT₁pos
    nlinarith
  nlinarith

end OneDim

/-! ### The cross-ratio distance decreases when the body grows -/

section Monotone

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set F} {u v : F}

/-- **`d_K(u,v)` is at most the cross-ratio distance of `u, v` in any sub-segment of the chord
that still contains them.**

If `[lineMap u v a₀, lineMap u v b₀] ⊆ K` with `a₀ ≤ 0 ≤ 1 ≤ b₀` — the segment `S` of the line
through `u, v` cut out by the parameters `a₀, b₀`, which contains `u` and `v` — then

    d_K(u,v) · ((−a₀)(b₀ − 1))  ≤  b₀ − a₀,

which is the division-free form of `d_K(u,v) ≤ d_S(u,v)`.  (Only the two *endpoints* of `S`
are asked to be in `K`; the rest of `S` is irrelevant, since the chord parameter set is an
interval.)

This is the step Lovász–Vempala perform silently when they pass from the hypothesis on
`d_K(u,v)` to the hypothesis of the one-dimensional inequality on the needle `[a,b] ⊆ K`:
the needle is shorter than the chord of `K`, so its own cross-ratio distances are *larger*.

Reading `a = chordLow ≤ a₀`, `b = chordHigh ≥ b₀` and putting `A = −a ≥ A₀ = −a₀ ≥ 0`,
`B = b − 1 ≥ B₀ = b₀ − 1 ≥ 0`, the claim is `(A+B+1)A₀B₀ ≤ (A₀+B₀+1)AB`, whose difference is
`A₀A(B−B₀) + B₀B(A−A₀) + (AB − A₀B₀) ≥ 0`. -/
theorem crossRatioDist_mul_le_of_lineMap_mem (hKb : Bornology.IsBounded K) (huv : u ≠ v)
    (hu : u ∈ K) (hv : v ∈ K) {a₀ b₀ : ℝ} (ha₀ : a₀ ≤ 0) (hb₀ : 1 ≤ b₀)
    (hmem₀ : (AffineMap.lineMap u v : ℝ → F) a₀ ∈ K)
    (hmem₁ : (AffineMap.lineMap u v : ℝ → F) b₀ ∈ K) :
    crossRatioDist K u v * (-a₀ * (b₀ - 1)) ≤ b₀ - a₀ := by
  have ha : chordLow K u v ≤ a₀ := csInf_le (bddBelow_chordParam hKb huv) hmem₀
  have hb : b₀ ≤ chordHigh K u v := le_csSup (bddAbove_chordParam hKb huv) hmem₁
  have haneg : chordLow K u v ≤ 0 := chordLow_nonpos hKb huv hu
  have hbone : 1 ≤ chordHigh K u v := one_le_chordHigh hKb huv hv
  have hRHS : 0 ≤ b₀ - a₀ := by linarith
  rw [crossRatioDist_eq_param hKb huv hu hv]
  set a := chordLow K u v with hadef
  set b := chordHigh K u v with hbdef
  rcases eq_or_lt_of_le haneg with h1 | h1
  · rw [h1, neg_zero, zero_mul, div_zero, zero_mul]; exact hRHS
  rcases eq_or_lt_of_le hbone with h2 | h2
  · rw [← h2, sub_self, mul_zero, div_zero, zero_mul]; exact hRHS
  have hden : (0 : ℝ) < -a * (b - 1) := mul_pos (by linarith) (by linarith)
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr ha₀) (by linarith : (0:ℝ) ≤ -a))
      (by linarith : (0:ℝ) ≤ (b - 1) - (b₀ - 1)),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ b₀ - 1) (by linarith : (0:ℝ) ≤ b - 1))
      (by linarith : (0:ℝ) ≤ -a - -a₀),
    mul_nonneg (by linarith : (0:ℝ) ≤ -a) (by linarith : (0:ℝ) ≤ b - 1),
    mul_nonneg (neg_nonneg.mpr ha₀) (by linarith : (0:ℝ) ≤ b₀ - 1)]

/-- Every point of a needle is on the chord through any two of its points: explicitly,
`needleMap p e r = lineMap (needleMap p e s) (needleMap p e t) ((r − s)/(t − s))`. -/
theorem lineMap_needleMap (p e : F) {s t : ℝ} (hst : s ≠ t) (r : ℝ) :
    (AffineMap.lineMap (needleMap p e s) (needleMap p e t) : ℝ → F) ((r - s) / (t - s))
      = needleMap p e r := by
  have hts : t - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hst)
  rw [lineMap_apply']
  simp only [needleMap]
  rw [show p + t • e - (p + s • e) = (t - s) • e by module, smul_smul,
    div_mul_cancel₀ _ hts]
  module

/-- **Transfer of a cross-ratio lower bound from the body to the needle.**

If `α ≤ s < t ≤ β`, the whole needle `[α, β]` lies in `K`, and `c ≤ d_K(u, v)` for
`u = needleMap p e s`, `v = needleMap p e t`, then `c` is also a lower bound for the cross-ratio
distance of `s` and `t` inside the *parameter interval* `[α, β]`, in division-free form:

    c · (s − α)(β − t)  ≤  (β − α)(t − s).

This is `Arlib.crossRatioDist_mul_le_of_lineMap_mem` at `a₀ = (α−s)/(t−s)`, `b₀ = (β−s)/(t−s)`,
cleared of denominators by `(t − s)²`. -/
theorem needle_crossRatio_transfer {K : Set F} (hKb : Bornology.IsBounded K) {p e : F}
    {α β s t c : ℝ} (hα : α ≤ s) (hst : s < t) (htβ : t ≤ β)
    (hαK : needleMap p e α ∈ K) (hβK : needleMap p e β ∈ K)
    (hsK : needleMap p e s ∈ K) (htK : needleMap p e t ∈ K)
    (hne : needleMap p e s ≠ needleMap p e t)
    (hc : c ≤ crossRatioDist K (needleMap p e s) (needleMap p e t)) :
    c * ((s - α) * (β - t)) ≤ (β - α) * (t - s) := by
  have hts : (0 : ℝ) < t - s := by linarith
  set a₀ : ℝ := (α - s) / (t - s) with ha₀def
  set b₀ : ℝ := (β - s) / (t - s) with hb₀def
  have ha₀ : a₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hts.le
  have hb₀ : 1 ≤ b₀ := (one_le_div hts).mpr (by linarith)
  have hmem₀ : (AffineMap.lineMap (needleMap p e s) (needleMap p e t) : ℝ → F) a₀ ∈ K := by
    rw [ha₀def, lineMap_needleMap p e (ne_of_lt hst) α]; exact hαK
  have hmem₁ : (AffineMap.lineMap (needleMap p e s) (needleMap p e t) : ℝ → F) b₀ ∈ K := by
    rw [hb₀def, lineMap_needleMap p e (ne_of_lt hst) β]; exact hβK
  have hfinal := crossRatioDist_mul_le_of_lineMap_mem hKb hne hsK htK ha₀ hb₀ hmem₀ hmem₁
  have hnn : 0 ≤ -a₀ * (b₀ - 1) := mul_nonneg (neg_nonneg.mpr ha₀) (by linarith)
  have hstep : c * (-a₀ * (b₀ - 1)) ≤ b₀ - a₀ :=
    le_trans (mul_le_mul_of_nonneg_right hc hnn) hfinal
  have hne' : t - s ≠ 0 := ne_of_gt hts
  have hL : (-a₀ * (b₀ - 1)) * (t - s) ^ 2 = (s - α) * (β - t) := by
    rw [ha₀def, hb₀def]; field_simp; ring
  have hR : (b₀ - a₀) * (t - s) ^ 2 = (β - α) * (t - s) := by
    rw [ha₀def, hb₀def]; field_simp; ring
  calc c * ((s - α) * (β - t)) = c * (-a₀ * (b₀ - 1)) * (t - s) ^ 2 := by rw [← hL]; ring
    _ ≤ (b₀ - a₀) * (t - s) ^ 2 := mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = (β - α) * (t - s) := hR

/-- **The needle's weight bound is at most a third of the cross-ratio distance of any cross
pair on it.**

If `u = needleMap p e s ∈ T₁` and `v = needleMap p e t ∈ T₂` then *every* point of the needle is
on the chord of `K` through `u` and `v`, so the hypothesis of Theorem 2.1 bounds `h` there by
`min(1, d_K(u,v))/3 ≤ d_K(u,v)/3`; the supremum of `h` along the needle therefore also is. -/
theorem three_mul_sSup_le_crossRatioDist {K T₁ T₂ : Set F} {h : F → ℝ}
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → F) r) → h x ≤ min 1 (crossRatioDist K u v) / 3)
    {p e : F} {α β : ℝ} (hαβ : α ≤ β) (hseg : ∀ r ∈ Set.Icc α β, needleMap p e r ∈ K)
    {s t : ℝ} (hs : needleMap p e s ∈ T₁) (ht : needleMap p e t ∈ T₂) (hst : s ≠ t) :
    3 * sSup ((fun r => h (needleMap p e r)) '' Set.Icc α β)
      ≤ crossRatioDist K (needleMap p e s) (needleMap p e t) := by
  set G : ℝ → ℝ := fun r => h (needleMap p e r) with hGdef
  have hne : (G '' Set.Icc α β).Nonempty := (Set.nonempty_Icc.mpr hαβ).image G
  have hub : ∀ y ∈ G '' Set.Icc α β,
      y ≤ crossRatioDist K (needleMap p e s) (needleMap p e t) / 3 := by
    rintro y ⟨r, hr, rfl⟩
    have hline : ∃ ρ : ℝ, needleMap p e r
        = (AffineMap.lineMap (needleMap p e s) (needleMap p e t) : ℝ → F) ρ :=
      ⟨(r - s) / (t - s), (lineMap_needleMap p e hst r).symm⟩
    have hb := hchord _ hs _ ht _ (hseg r hr) hline
    have hm := min_le_right (1 : ℝ) (crossRatioDist K (needleMap p e s) (needleMap p e t))
    simp only [hGdef]
    linarith
  have := csSup_le hne hub
  linarith

end Monotone

/-! ### Theorem 2.1 transported to a needle -/

section Ambient

variable {n : ℕ}

/-- **Theorem 2.1 of Lovász–Vempala, on a needle inside the body.**

`K` is a bounded body, `T₁, T₂ ⊆ K` are disjoint measurable sets, and `h ≥ 0` satisfies the
hypothesis of Theorem 2.1 — bounded by `min(1, d_K(u,v))/3` on the chord through any cross pair
— **together with the global bound `h ≤ 1/3` on `K`** (see the module docstring: the global
bound is not a consequence of the chord bound, and Theorem 2.1 is false without it).

Then, for any needle `t ↦ p + t·e` whose parameter interval `[α, β]` maps into `K`, carrying a
log-concave weight `D` with `∫_{Z₁} D = A·∫_α^β D` for some `0 ≤ A ≤ 1/2`,

    A · ∫_α^β h(needle t)·D(t) dt  ≤  ∫_{Z₃} D,

where `Z₁, Z₃` are the parameters landing in `T₁` and in `K ∖ T₁ ∖ T₂`.  This is precisely the
inequality that the Localization Lemma is invoked to contradict. -/
theorem needle_iso_of_chord {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hdisj : Disjoint T₁ T₂)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3)
    {p e : EuclideanSpace ℝ (Fin n)} {α β : ℝ} (hαβ : α ≤ β)
    (hseg : ∀ r ∈ Set.Icc α β, needleMap p e r ∈ K)
    {D : ℝ → ℝ} (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t) (hlc : LogConcaveOn (Set.Icc α β) D)
    (hDint : IntervalIntegrable D volume α β)
    (hGDint : IntervalIntegrable (fun t => h (needleMap p e t) * D t) volume α β)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 1 / 2)
    (hmass : (∫ t in needleMap p e ⁻¹' T₁ ∩ Set.Icc α β, D t) = A * ∫ t in α..β, D t) :
    A * (∫ t in α..β, h (needleMap p e t) * D t)
      ≤ ∫ t in needleMap p e ⁻¹' ((K \ T₁) \ T₂) ∩ Set.Icc α β, D t := by
  classical
  have hcont : Continuous (needleMap p e) := by
    show Continuous fun t : ℝ => p + t • e
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hmeas : Measurable (needleMap p e) := hcont.measurable
  set Z₁ := needleMap p e ⁻¹' T₁ ∩ Set.Icc α β with hZ₁def
  set Z₂ := needleMap p e ⁻¹' T₂ ∩ Set.Icc α β with hZ₂def
  set Z₃ := needleMap p e ⁻¹' ((K \ T₁) \ T₂) ∩ Set.Icc α β with hZ₃def
  have hm₁ : MeasurableSet Z₁ := (hT₁.preimage hmeas).inter measurableSet_Icc
  have hm₂ : MeasurableSet Z₂ := (hT₂.preimage hmeas).inter measurableSet_Icc
  -- the three parameter sets partition `[α, β]`
  have hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine Set.Subset.antisymm ?_ ?_
      · rintro r ((⟨-, hr⟩ | ⟨-, hr⟩) | ⟨-, hr⟩) <;> exact hr
      · intro r hr
        by_cases h1 : needleMap p e r ∈ T₁
        · exact Or.inl (Or.inl ⟨h1, hr⟩)
        by_cases h2 : needleMap p e r ∈ T₂
        · exact Or.inl (Or.inr ⟨h2, hr⟩)
        · exact Or.inr ⟨⟨⟨hseg r hr, h1⟩, h2⟩, hr⟩
    · exact Set.disjoint_left.mpr fun r hr₁ hr₂ =>
        Set.disjoint_left.mp hdisj hr₁.1 hr₂.1
    · exact Set.disjoint_left.mpr fun r hr₁ hr₃ => hr₃.1.1.2 hr₁.1
    · exact Set.disjoint_left.mpr fun r hr₂ hr₃ => hr₃.1.2 hr₂.1
  have hm₃ : MeasurableSet Z₃ := by
    have : Z₃ = Set.Icc α β \ (Z₁ ∪ Z₂) := by
      refine Set.Subset.antisymm (fun r hr => ⟨hr.2, ?_⟩) (fun r hr => ?_)
      · rintro (h1 | h2)
        exacts [hr.1.1.2 h1.1, hr.1.2 h2.1]
      · have hr3 : r ∈ Z₁ ∪ Z₂ ∪ Z₃ := by rw [hpart.union]; exact hr.1
        rcases hr3 with (h1 | h2) | h3
        exacts [absurd (Or.inl h1) hr.2, absurd (Or.inr h2) hr.2, h3]
    rw [this]
    exact measurableSet_Icc.diff (hm₁.union hm₂)
  -- the supremum of `h` along the needle
  set M := sSup ((fun r => h (needleMap p e r)) '' Set.Icc α β) with hMdef
  have hIccne : (Set.Icc α β).Nonempty := Set.nonempty_Icc.mpr hαβ
  have hbdd : BddAbove ((fun r => h (needleMap p e r)) '' Set.Icc α β) := by
    refine ⟨1 / 3, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact hh3 _ (hseg r hr)
  have hGM : ∀ r ∈ Set.Icc α β, h (needleMap p e r) ≤ M := fun r hr =>
    le_csSup hbdd ⟨r, hr, rfl⟩
  have hM3 : M ≤ 1 / 3 := by
    refine csSup_le (hIccne.image _) ?_
    rintro y ⟨r, hr, rfl⟩
    exact hh3 _ (hseg r hr)
  have hM0 : 0 ≤ M := le_trans (hh0 _) (hGM α ⟨le_rfl, hαβ⟩)
  -- the cross condition on the needle
  have hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂,
      3 * M * ((min s t - α) * (β - max s t)) ≤ (β - α) * (max s t - min s t) := by
    intro s hs t ht
    have hsK : needleMap p e s ∈ K := hseg s hs.2
    have htK : needleMap p e t ∈ K := hseg t ht.2
    have hnee : needleMap p e s ≠ needleMap p e t := fun heq =>
      Set.disjoint_left.mp hdisj hs.1 (heq ▸ ht.1)
    have hst : s ≠ t := fun heq => hnee (by rw [heq])
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
      refine needle_crossRatio_transfer hKb hs.2.1 hlt ht.2.2
        (hseg α ⟨le_rfl, hαβ⟩) (hseg β ⟨hαβ, le_rfl⟩) hsK htK hnee ?_
      exact three_mul_sSup_le_crossRatioDist hchord hαβ hseg hs.1 ht.1 hst
    · rw [min_eq_right hgt.le, max_eq_left hgt.le]
      refine needle_crossRatio_transfer hKb ht.2.1 hgt hs.2.2
        (hseg α ⟨le_rfl, hαβ⟩) (hseg β ⟨hαβ, le_rfl⟩) htK hsK (Ne.symm hnee) ?_
      rw [crossRatioDist_comm hKb (Ne.symm hnee) htK hsK]
      exact three_mul_sSup_le_crossRatioDist hchord hαβ hseg hs.1 ht.1 hst
  exact needle_iso hαβ hD0 hlc hDint hGM hM0 hM3 hGDint hpart hm₁ hm₂ hm₃ hA0 hA hmass hcross

/-- **Theorem 2.1 of Lovász–Vempala for the uniform density, modulo the Localization Lemma.**

Every hypothesis below is either geometry (discharged) or the single binder `hloc`, which is
Corollary 2.4 of Kannan–Lovász–Simonovits 1995 applied to the signed pair

    g₁ = 1_{T₁} − A·1_K,     g₂ = A·h·1_K − 1_{K∖T₁∖T₂}

— `∫ g₁ = 0` by `hmassK`, `∫ g₂ > 0` by the assumption being contradicted — and delivers the
needle `t ↦ p + t·e`, its parameter interval `[α, β]` and its weight `D = ℓ^{n−1}` with the two
relations transported.  Compare `Arlib.gaussianRestricted_isoperimetry`'s `hloc`, which has the
same shape for the Gaussian-restricted density.

The conclusion is `A·∫_K h ≤ vol(K ∖ T₁ ∖ T₂)`; at `A = vol T₁ / vol K` (which is `≤ 1/2`
exactly when `vol T₁ ≤ vol T₂`, since `T₁` and `T₂` are disjoint subsets of `K`) this is
Theorem 2.1 in the form `π(S₃) ≥ E_π(h)·min(π S₁, π S₂)` for the uniform `π`.

**`hh3` is not in the paper's statement and Theorem 2.1 is false without it** — see the module
docstring. -/
theorem thm21_of_localization {K T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) (hdisj : Disjoint T₁ T₂)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh3 : ∀ x ∈ K, h x ≤ 1 / 3)
    (hchord : ∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
      (∃ r : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) r) →
      h x ≤ min 1 (crossRatioDist K u v) / 3)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 1 / 2)
    (hmassK : (volume T₁).toReal = A * (volume K).toReal)
    (hloc : (volume T₁).toReal = A * (volume K).toReal →
      (volume ((K \ T₁) \ T₂)).toReal < A * ∫ x in K, h x →
      ∃ (p e : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (D : ℝ → ℝ), α ≤ β ∧
        (∀ r ∈ Set.Icc α β, needleMap p e r ∈ K) ∧
        (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ LogConcaveOn (Set.Icc α β) D ∧
        IntervalIntegrable D volume α β ∧
        IntervalIntegrable (fun t => h (needleMap p e t) * D t) volume α β ∧
        (∫ t in needleMap p e ⁻¹' T₁ ∩ Set.Icc α β, D t) = A * ∫ t in α..β, D t ∧
        (∫ t in needleMap p e ⁻¹' ((K \ T₁) \ T₂) ∩ Set.Icc α β, D t)
          < A * ∫ t in α..β, h (needleMap p e t) * D t) :
    A * (∫ x in K, h x) ≤ (volume ((K \ T₁) \ T₂)).toReal := by
  by_contra hcon
  obtain ⟨p, e, α, β, D, hαβ, hseg, hD0, hlc, hDint, hGDint, hmass, hstrict⟩ :=
    hloc hmassK (not_le.mp hcon)
  exact absurd (needle_iso_of_chord hKb hT₁ hT₂ hdisj hh0 hh3 hchord hαβ hseg hD0 hlc hDint
    hGDint hA0 hA hmass) (not_le.mpr hstrict)

end Ambient

/-! ### The counterexample of §1 of the module docstring, certified -/

section Counterexample

/-- **No chord through `[0,1/8]² × [7/8,1]×[0,1/8]` reaches height `1/3` inside the unit
square.**

This is the geometric core of the counterexample to Theorem 2.1 recorded in the module
docstring: for `u ∈ S₁ = [0,1/8]²`, `v ∈ S₂ = [7/8,1] × [0,1/8]` and `x` a point of the chord
through `u` and `v` whose first coordinate lies in `[0,1]` (in particular any `x ∈ K = [0,1]²`),

    x₁ ≤ 7/24 < 1/3.

Hence `h = M·1_N` with `N = K ∩ {x₁ > 1/3}` — a set of measure `2/3` — satisfies the hypothesis
of Theorem 2.1 for *every* `M ≥ 0`, while `E(h)·min{vol S₁, vol S₂} = M/96` is unbounded and
`vol S₃ = 31/32`.  The chord hypothesis is `h x ≤ (1/3)·min(1, d_K(u,v))`, and `h x = 0` at
every such `x` because `x ∉ N`; `Arlib.crossRatioDist_nonneg` makes the right-hand side
nonnegative, so the hypothesis holds. -/
theorem chord_le_of_corner_boxes {u v x : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hu0 : u 0 ∈ Set.Icc (0 : ℝ) (1 / 8)) (hu1 : u 1 ∈ Set.Icc (0 : ℝ) (1 / 8))
    (hv0 : v 0 ∈ Set.Icc (7 / 8 : ℝ) 1) (hv1 : v 1 ∈ Set.Icc (0 : ℝ) (1 / 8))
    (hx0 : x 0 ∈ Set.Icc (0 : ℝ) 1)
    (hxr : x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin 2)) r) :
    x 1 ≤ 7 / 24 := by
  obtain ⟨hu0a, hu0b⟩ := hu0
  obtain ⟨hu1a, hu1b⟩ := hu1
  obtain ⟨hv0a, hv0b⟩ := hv0
  obtain ⟨hv1a, hv1b⟩ := hv1
  obtain ⟨hx0a, hx0b⟩ := hx0
  have hcoord : ∀ i, x i = r * (v i - u i) + u i := by
    intro i
    rw [hxr, lineMap_apply']
    simp
  have h0 := hcoord 0
  have h1 := hcoord 1
  have hgap : (3 : ℝ) / 4 ≤ v 0 - u 0 := by linarith
  -- `r ≤ 4/3` and `-1/6 ≤ r`, from `r·(v₀−u₀) = x₀ − u₀ ∈ [−1/8, 1]`
  have hup : r ≤ 4 / 3 := by nlinarith
  have hlow : -(1 / 6 : ℝ) ≤ r := by nlinarith
  have hv1u1 : |v 1 - u 1| ≤ 1 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  rcases le_or_gt 0 r with hr | hr
  · nlinarith
  · nlinarith

end Counterexample

/-! ### Non-vacuity -/

section Witness

/-- The three parts of the witness below really do partition `[0,1]`. -/
theorem witness_isPartition3 :
    IsPartition3 (Set.Icc (0 : ℝ) 1) (Set.Icc 0 (1 / 4)) (Set.Icc (3 / 4) 1)
      (Set.Ioo (1 / 4) (3 / 4)) := by
  refine ⟨Set.Subset.antisymm ?_ ?_, ?_, ?_, ?_⟩
  · rintro x ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) <;> constructor <;> linarith
  · rintro x ⟨h1, h2⟩
    rcases le_or_gt x (1 / 4) with h | h
    · exact Or.inl (Or.inl ⟨h1, h⟩)
    rcases lt_or_ge x (3 / 4) with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl (Or.inr ⟨h', h2⟩)
  · exact Set.disjoint_left.mpr fun x hx hx' => by
      have := hx.2; have := hx'.1; linarith
  · exact Set.disjoint_left.mpr fun x hx hx' => by
      have := hx.2; have := hx'.1; linarith
  · exact Set.disjoint_left.mpr fun x hx hx' => by
      have := hx.1; have := hx'.2; linarith

/-- **Non-vacuity of `Arlib.oneDim_crossRatio_partition`**: every hypothesis is satisfiable at
once, with a strictly positive left-hand side.  Uniform weight on `[0,1]`, `Z₁ = [0,1/4]`,
`Z₂ = [3/4,1]`, `Z₃ = (1/4,3/4)` and `c = 1`; the inequality reads `1/16 ≤ 1/2`. -/
theorem oneDim_crossRatio_partition_witness :
    (1 : ℝ) * ((∫ _t in Set.Icc (0 : ℝ) (1 / 4), (1 : ℝ)) *
        ∫ _t in Set.Icc (3 / 4 : ℝ) 1, (1 : ℝ))
      ≤ (∫ _t in (0 : ℝ)..1, (1 : ℝ)) * ∫ _t in Set.Ioo (1 / 4 : ℝ) (3 / 4), (1 : ℝ) := by
  refine oneDim_crossRatio_partition (by norm_num) (fun t _ => zero_le_one)
    (logConcaveOn_const (convex_Icc 0 1) zero_le_one) intervalIntegrable_const
    witness_isPartition3 measurableSet_Icc measurableSet_Icc measurableSet_Ioo ?_
  rintro s ⟨hs1, hs2⟩ t ⟨ht1, ht2⟩
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  nlinarith

/-- The left-hand side of the witness is `1/16`, so the witness is not vacuous. -/
theorem oneDim_crossRatio_partition_witness_pos :
    (0 : ℝ) < (1 : ℝ) * ((∫ _t in Set.Icc (0 : ℝ) (1 / 4), (1 : ℝ)) *
      ∫ _t in Set.Icc (3 / 4 : ℝ) 1, (1 : ℝ)) := by
  rw [setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def, Real.volume_Icc]
  norm_num

/-- **Non-vacuity of `Arlib.needle_iso`** — the main one-dimensional statement.  Uniform weight
on `[0,1]`, the partition of `Arlib.witness_isPartition3`, `G ≡ 0`, `M = 0` and `A = 1/4`; every
hypothesis is discharged and the conclusion reads `0 ≤ 1/2`.  In particular the hypothesis
`∫_{Z₁} D = A·∫_α^β D` is satisfiable with `A > 0` and a nondegenerate partition. -/
theorem needle_iso_witness :
    (1 / 4 : ℝ) * (∫ t in (0 : ℝ)..1, (0 : ℝ) * (1 : ℝ))
      ≤ ∫ _t in Set.Ioo (1 / 4 : ℝ) (3 / 4), (1 : ℝ) := by
  have hmass : (∫ _t in Set.Icc (0 : ℝ) (1 / 4), (1 : ℝ))
      = (1 / 4 : ℝ) * ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
    rw [setIntegral_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def, Real.volume_Icc]
    norm_num
  refine needle_iso (D := fun _ => (1 : ℝ)) (G := fun _ => (0 : ℝ)) (by norm_num)
    (fun t _ => zero_le_one) (logConcaveOn_const (convex_Icc 0 1) zero_le_one)
    intervalIntegrable_const (fun t _ => le_rfl) le_rfl (by norm_num)
    (by simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℝ) * (1 : ℝ))
      volume 0 1))
    witness_isPartition3 measurableSet_Icc measurableSet_Icc measurableSet_Ioo (by norm_num)
    (by norm_num) hmass ?_
  intro s _ t _
  norm_num

end Witness

/-! ### Axiom audit -/

section AxiomCheck

#print axioms Arlib.isLogConcave_indicator_of_logConcaveOn
#print axioms Arlib.crossRatioIcc_mul_le
#print axioms Arlib.oneDim_crossRatio_partition
#print axioms Arlib.needle_iso
#print axioms Arlib.crossRatioDist_mul_le_of_lineMap_mem
#print axioms Arlib.needle_crossRatio_transfer
#print axioms Arlib.three_mul_sSup_le_crossRatioDist
#print axioms Arlib.needle_iso_of_chord
#print axioms Arlib.thm21_of_localization
#print axioms Arlib.chord_le_of_corner_boxes
#print axioms Arlib.oneDim_crossRatio_partition_witness
#print axioms Arlib.needle_iso_witness

end AxiomCheck

end Arlib
