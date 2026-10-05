/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.OneDimIsoperimetry

/-!
# From interval triples to measurable partitions in one dimension

Cousins–Vempala dispose of one step of the proof of `thm:iso` in a single sentence
(`1409.6011/vol3_journal.tex:497`):

> "By a standard combinatorial argument, we can assume that `Zᵢ = {t : (1−t)a+tb ∈ Sᵢ}` are
> intervals that partition `[a,b]`."

This file is about the *content* of that sentence: the passage from the **interval** case of
the one-dimensional isoperimetric inequality — which is what the Localization Lemma and
`(1d-1)`/`(1d-2)` deliver — to an arbitrary **measurable** three-way partition, which is what
the proof actually consumes.  It is the hypothesis called `hcombinatorial` in
`Arlib.Convexity.SharpIsoperimetry`.

## Main results

* `Arlib.oneDim_partition_of_side` — **the theorem proved here.**  The interval case implies
  the measurable-partition case whenever `Z₁` lies weakly to the left of `Z₂`.
* `Arlib.oneDim_partition_of_unmixed` — the same with the two orientations combined.
* `Arlib.nonneg_csSup_csInf` — the analytic step: a continuous inequality valid on `S ×ˢ T`
  is still valid at `(sSup S, sInf T)`.
* `Arlib.oneDim_partition_witness` — non-vacuity: concrete data satisfying **every**
  hypothesis of `Arlib.oneDim_partition_of_side` at once, with a strictly positive left-hand
  side.
* `Arlib.cousinsVempala_counterexample_c_le` — the acid test: for the configuration recorded
  in `Arlib.Convexity.SharpIsoperimetry` (the one that refutes the literal reading of the
  paper's sentence), the separation hypothesis `hcross` forces `c ≤ 5/18`, so it is **not**
  satisfiable at the `c = 4` of that counterexample.
* `Arlib.hside_not_implied` — the honest boundary of this file: `hcross` does **not** force
  `Z₁` to lie on one side of `Z₂`, so `Arlib.oneDim_partition_of_side` is strictly weaker
  than `hcombinatorial`.  See "What is still open" below.

## Why the literal reading is false, and what replaces it

Taking `D ≡ 1` on `[0,1]`, `A = 0.8`, `c = 4` and

  `Z₁ = [0,0.4] ∪ [0.6,1]`,  `Z₂ = (0.45,0.5)`,  `Z₃` the rest,

both post-localisation relations hold (`∫_{Z₁} = 0.8 = A·∫`, `∫_{Z₃} = 0.15 < c·A·∫_{Z₂} =
0.16`) yet neither orientation of an interval reduction exists: `∫_0^u = 0.8` forces `u = 0.8`
and no point of `Z₂` lies to its right, while `∫_v^1 = 0.8` forces `v = 0.2` and no point of
`Z₂` lies to its left.  So "we can assume that the `Zᵢ` are intervals" is not a statement one
can prove — it is false.

What the real argument has and the literal reading drops is the **separation** between `Z₁`
and `Z₂`, which is a hypothesis of `thm:iso` (`‖u−v‖ ≥ d/ln 2` or `d_h(u,v) ≥ 4(d/σ)√n`).
Carried into one dimension it becomes the hypothesis `hcross` below: the interval-case
coefficient `κ` is at least `c` on every *cross pair* `(s,t) ∈ Z₁ × Z₂`.
`Arlib.cousinsVempala_counterexample_c_le` checks that this really does exclude the
configuration above: the cross pair `(0.4, 0.46)` and the interval case at `(0.4, 0.46)`
together force `c ≤ 5/18 < 4`.

## The shape of the argument

Write `G x = ∫_α^x D` and `M = ∫_α^β D`.  For a cross pair `(s,t)` with `s ≤ t`, the interval
case at `(s,t)` and `c ≤ κ s t` give

  `c · G s · (M − G t) ≤ M · (G t − G s)`.                                    (★)

Both sides of (★) are *continuous* in `(s,t)`, so (★) survives passing to the closure of
`Z₁ ×ˢ Z₂`, and in particular holds at `(u,v) := (sSup Z₁, sInf Z₂)` — even though `κ` itself
is an arbitrary function with no continuity whatsoever.  This is
`Arlib.nonneg_csSup_csInf`, and it is the only analysis in the file.

If `Z₁` lies weakly to the left of `Z₂` then `u ≤ v`, and then

  `∫_{Z₁} D ≤ G u`,  `∫_{Z₂} D ≤ M − G v`,  `G v − G u ≤ ∫_{Z₃} D`,

the last because `(u,v)` misses `Z₁` (above its sup) and misses `Z₂` (below its inf), hence
lies in `Z₃`.  Chaining these three with (★) is the conclusion.

## What is still open

`Arlib.hside_not_implied` exhibits data satisfying every hypothesis of `hcombinatorial` —
including `hcross` — in which `Z₁` lies on **both** sides of `Z₂`: with `D ≡ 1` on `[0,1]`,

  `Z₁ = [0.1,0.4] ∪ [0.6,0.9]`,  `Z₂ = (0.45,0.5)`,  `c = 5/22`.

So separation does **not** make the configuration one-sided, and the one-sidedness hypothesis
`hside` of `Arlib.oneDim_partition_of_side` is a genuine restriction: this file does *not*
discharge `hcombinatorial`.  What is missing is exactly the interleaved case.

In the coordinates that make the problem transparent — substituting `x = F(t)` for the
normalised primitive `F = G/M`, and then `ξ = log(x/(1−x))` — the hypothesis `hcross` becomes
metric separation `|ξ(s) − ξ(t)| ≥ log(1+c)` and the conclusion becomes the classical
one-dimensional isoperimetric inequality for the logistic measure.  The general case then
follows from the one-sided case applied to each connected component of the open
`log(1+c)`-neighbourhood of `Z₁`, using that `T(x) = (1+c)x/(1+cx)` is concave with `T 0 = 0`,
hence subadditive, together with the Möbius inequality `T q − T⁻¹ p ≥ T (q − p)`.  That route
needs a decomposition of an open subset of `ℝ` into its countably many components and a
countable subadditivity argument; it is not carried out here.

## No rate claim

Nothing in this file says, or implies, that any algorithm runs in polynomial time.  It is a
conditional reduction between two forms of a one-dimensional inequality.

## References

Cousins and Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and Gaussian Volume*,
§3 (`1409.6011/vol3_journal.tex:404–508`; the sentence formalised here is line 497).

Lovász and Simonovits, *Random walks in a convex body and an improved volume algorithm*,
Random Structures & Algorithms **4** (1993).
-/

namespace Arlib

open MeasureTheory Set

/-! ### The analytic step: a continuous inequality passes to `sSup` and `sInf` -/

section Closure

/-- **A continuous inequality valid on `S ×ˢ T` is valid at `(sSup S, sInf T)`.**

This is what lets an inequality known only at *points* of `Z₁` and `Z₂` be evaluated at the
endpoints `sSup Z₁` and `sInf Z₂` of the interval triple, without assuming anything at all
about the coefficient function `κ` that produced it: the inequality is transported, not the
coefficient. -/
theorem nonneg_csSup_csInf {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous fun p : ℝ × ℝ => Φ p.1 p.2)
    {S T : Set ℝ} (hS : S.Nonempty) (hSb : BddAbove S) (hT : T.Nonempty) (hTb : BddBelow T)
    (h : ∀ s ∈ S, ∀ t ∈ T, 0 ≤ Φ s t) : 0 ≤ Φ (sSup S) (sInf T) := by
  have hsub : closure (S ×ˢ T) ⊆ {p : ℝ × ℝ | 0 ≤ Φ p.1 p.2} :=
    closure_minimal (by rintro ⟨s, t⟩ ⟨hs, ht⟩; exact h s hs t ht)
      (isClosed_le continuous_const hΦ)
  have hmem : ((sSup S : ℝ), (sInf T : ℝ)) ∈ closure (S ×ˢ T) := by
    rw [closure_prod_eq]
    exact ⟨csSup_mem_closure hS hSb, csInf_mem_closure hT hTb⟩
  exact hsub hmem

end Closure

/-! ### Comparing set integrals with interval integrals -/

section Compare

variable {g : ℝ → ℝ}

/-- The integral of a nonnegative integrable function over a subset of `[a,x]` is at most its
interval integral over `[a,x]`. -/
theorem setIntegral_le_intervalIntegral (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t) {S : Set ℝ}
    {a x : ℝ} (hax : a ≤ x) (hS : S ⊆ Set.Icc a x) : (∫ t in S, g t) ≤ ∫ t in a..x, g t := by
  have h1 : (∫ t in S, g t) ≤ ∫ t in Set.Icc a x, g t :=
    setIntegral_mono_set hg.integrableOn (Filter.Eventually.of_forall hg0) hS.eventuallyLE
  rwa [intervalIntegral.integral_of_le hax, ← integral_Icc_eq_integral_Ioc]

/-- The interval integral of a nonnegative integrable function over `[u,v]` is at most its
integral over any set containing the open interval `(u,v)`. -/
theorem intervalIntegral_le_setIntegral (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t) {S : Set ℝ}
    {u v : ℝ} (huv : u ≤ v) (hS : Set.Ioo u v ⊆ S) : (∫ t in u..v, g t) ≤ ∫ t in S, g t := by
  rw [intervalIntegral.integral_of_le huv, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_mono_set hg.integrableOn (Filter.Eventually.of_forall hg0) hS.eventuallyLE

end Compare

/-! ### The reduction -/

section Reduction

/-- **The interval case of the one-dimensional isoperimetric inequality implies the
measurable-partition case, for a one-sided configuration.**

Let `D ≥ 0` be interval-integrable on `[α,β]` and let `Z₁, Z₂, Z₃` be a measurable three-way
partition of `[α,β]`.  Assume:

* `hint` — the inequality for every **interval triple**: for `α ≤ x ≤ y ≤ β`,
  `κ x y · (∫_α^x D)(∫_y^β D) ≤ (∫_α^β D)(∫_x^y D)`;
* `hcross` — **separation**: `c ≤ κ` on every cross pair of `Z₁ × Z₂`;
* `hside` — every point of `Z₁` is at most every point of `Z₂`.

Then `c · (∫_{Z₁} D)(∫_{Z₂} D) ≤ (∫_α^β D)(∫_{Z₃} D)`.

`hcross` is not removable: without it the statement is false, and
`Arlib.cousinsVempala_counterexample_c_le` records the refuting configuration.  `hside` is
also not removable *by this proof*, and is not implied by the remaining hypotheses —
see `Arlib.hside_not_implied` and the module docstring. -/
theorem oneDim_partition_of_side (D : ℝ → ℝ) (Z₁ Z₂ Z₃ : Set ℝ) (κ : ℝ → ℝ → ℝ) (α β c : ℝ)
    (hαβ : α ≤ β) (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t)
    (hDint : IntervalIntegrable D volume α β)
    (hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃)
    (hmZ₁ : MeasurableSet Z₁) (hmZ₂ : MeasurableSet Z₂) (hmZ₃ : MeasurableSet Z₃)
    (hint : ∀ x y : ℝ, α ≤ x → x ≤ y → y ≤ β →
      κ x y * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
        ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t)
    (hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂, c ≤ κ (min s t) (max s t))
    (hside : ∀ s ∈ Z₁, ∀ t ∈ Z₂, s ≤ t) :
    c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t) ≤ (∫ t in α..β, D t) * ∫ t in Z₃, D t := by
  classical
  have hZ1sub : Z₁ ⊆ Set.Icc α β := hpart.subset₁
  have hZ2sub : Z₂ ⊆ Set.Icc α β := hpart.subset₂
  have hZ3sub : Z₃ ⊆ Set.Icc α β := hpart.subset₃
  -- the three set masses, and the total mass, are nonnegative
  have ha1nn : 0 ≤ ∫ t in Z₁, D t := setIntegral_nonneg hmZ₁ fun t ht => hD0 t (hZ1sub ht)
  have ha2nn : 0 ≤ ∫ t in Z₂, D t := setIntegral_nonneg hmZ₂ fun t ht => hD0 t (hZ2sub ht)
  have ha3nn : 0 ≤ ∫ t in Z₃, D t := setIntegral_nonneg hmZ₃ fun t ht => hD0 t (hZ3sub ht)
  have hMnn : 0 ≤ ∫ t in α..β, D t :=
    intervalIntegral.integral_nonneg hαβ fun t ht => hD0 t ht
  have hRHS : 0 ≤ (∫ t in α..β, D t) * ∫ t in Z₃, D t := mul_nonneg hMnn ha3nn
  -- `c < 0` is trivial
  rcases lt_or_ge c 0 with hcneg | hc0
  · have : c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcneg.le (mul_nonneg ha1nn ha2nn)
    linarith
  -- an empty part is trivial
  rcases Set.eq_empty_or_nonempty Z₁ with hZ1e | hZ1n
  · rw [hZ1e]; simpa using hRHS
  rcases Set.eq_empty_or_nonempty Z₂ with hZ2e | hZ2n
  · rw [hZ2e]; simpa using hRHS
  -- the weight, truncated to `[α,β]`, so that its primitive is globally continuous
  set Dc : ℝ → ℝ := (Set.Icc α β).indicator D with hDcdef
  have hDc0 : ∀ t, 0 ≤ Dc t := Set.indicator_nonneg fun s hs => hD0 s hs
  have hDcI : Integrable Dc :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hαβ).mp hDint)
  have hDceq : ∀ t ∈ Set.Icc α β, Dc t = D t := fun t ht => Set.indicator_of_mem ht D
  have hII : ∀ x y : ℝ, x ∈ Set.Icc α β → y ∈ Set.Icc α β →
      (∫ t in x..y, Dc t) = ∫ t in x..y, D t := fun x y hx hy =>
    intervalIntegral.integral_congr fun t ht => hDceq t (Set.uIcc_subset_Icc hx hy ht)
  have hSI : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Set.Icc α β →
      (∫ t in S, Dc t) = ∫ t in S, D t := fun S hS hsub =>
    setIntegral_congr_fun hS fun t ht => hDceq t (hsub ht)
  -- the primitive
  set G : ℝ → ℝ := fun x => ∫ t in α..x, Dc t with hGdef
  have hGcont : Continuous G := hDcI.continuous_primitive α
  set M : ℝ := G β with hMdef
  have hMeq : M = ∫ t in α..β, D t := hII α β ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩
  have hGsub : ∀ x y : ℝ, (∫ t in x..y, Dc t) = G y - G x := by
    intro x y
    have := intervalIntegral.integral_add_adjacent_intervals
      (a := α) (b := x) (c := y) (f := Dc) hDcI.intervalIntegrable hDcI.intervalIntegrable
    simp only [hGdef]
    linarith
  have hGmono : ∀ x y : ℝ, x ≤ y → G x ≤ G y := by
    intro x y hxy
    have h1 : (0:ℝ) ≤ ∫ t in x..y, Dc t :=
      intervalIntegral.integral_nonneg hxy fun t _ => hDc0 t
    rw [hGsub] at h1; linarith
  have hGα : G α = 0 := by simp [hGdef]
  -- the endpoints of the interval triple
  have hbdd1 : BddAbove Z₁ := bddAbove_Icc.mono hZ1sub
  have hbdd2 : BddBelow Z₂ := bddBelow_Icc.mono hZ2sub
  set u : ℝ := sSup Z₁ with hudef
  set v : ℝ := sInf Z₂ with hvdef
  obtain ⟨s₀, hs₀⟩ := hZ1n
  obtain ⟨t₀, ht₀⟩ := hZ2n
  have hαu : α ≤ u := le_trans (hZ1sub hs₀).1 (le_csSup hbdd1 hs₀)
  have huβ : u ≤ β := csSup_le ⟨s₀, hs₀⟩ fun s hs => (hZ1sub hs).2
  have hαv : α ≤ v := le_csInf ⟨t₀, ht₀⟩ fun t ht => (hZ2sub ht).1
  have hvβ : v ≤ β := le_trans (csInf_le hbdd2 ht₀) (hZ2sub ht₀).2
  have huv : u ≤ v := csSup_le ⟨s₀, hs₀⟩ fun s hs => le_csInf ⟨t₀, ht₀⟩ fun t ht => hside s hs t ht
  -- (★) at the endpoints, obtained from (★) at cross pairs by continuity
  have hstar : 0 ≤ M * (G v - G u) - c * (G u * (M - G v)) := by
    refine nonneg_csSup_csInf (Φ := fun s t => M * (G t - G s) - c * (G s * (M - G t)))
      ?_ ⟨s₀, hs₀⟩ hbdd1 ⟨t₀, ht₀⟩ hbdd2 ?_
    · have hc1 : Continuous fun p : ℝ × ℝ => G p.1 := hGcont.comp continuous_fst
      have hc2 : Continuous fun p : ℝ × ℝ => G p.2 := hGcont.comp continuous_snd
      exact (continuous_const.mul (hc2.sub hc1)).sub
        (continuous_const.mul (hc1.mul (continuous_const.sub hc2)))
    · intro s hs t ht
      have hsI := hZ1sub hs
      have htI := hZ2sub ht
      have hst : s ≤ t := hside s hs t ht
      have hκ : c ≤ κ s t := by
        have h := hcross s hs t ht
        rwa [min_eq_left hst, max_eq_right hst] at h
      have hi := hint s t hsI.1 hst htI.2
      rw [← hII α s ⟨le_rfl, hαβ⟩ hsI, ← hII t β htI ⟨hαβ, le_rfl⟩,
        ← hII α β ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩, ← hII s t hsI htI] at hi
      simp only [hGsub, hGα, sub_zero, ← hMdef] at hi
      have hGs : 0 ≤ G s := by have := hGmono α s hsI.1; rw [hGα] at this; exact this
      have hGt : G t ≤ M := by rw [hMdef]; exact hGmono t β htI.2
      have hprod : 0 ≤ G s * (M - G t) := mul_nonneg hGs (by linarith)
      have hmono := mul_le_mul_of_nonneg_right hκ hprod
      linarith
  -- the three mass comparisons
  have ha1u : (∫ t in Z₁, D t) ≤ G u := by
    rw [← hSI Z₁ hmZ₁ hZ1sub]
    have := setIntegral_le_intervalIntegral (g := Dc) hDcI hDc0 (S := Z₁) (a := α) (x := u)
      hαu fun s hs => ⟨(hZ1sub hs).1, le_csSup hbdd1 hs⟩
    rw [hGsub, hGα] at this; simpa using this
  have ha2v : (∫ t in Z₂, D t) ≤ M - G v := by
    rw [← hSI Z₂ hmZ₂ hZ2sub]
    have := setIntegral_le_intervalIntegral (g := Dc) hDcI hDc0 (S := Z₂) (a := v) (x := β)
      hvβ fun t ht => ⟨csInf_le hbdd2 ht, (hZ2sub ht).2⟩
    rw [hGsub, ← hMdef] at this; exact this
  have hIoo : Set.Ioo u v ⊆ Z₃ := by
    intro x hx
    have hxI : x ∈ Set.Icc α β := ⟨le_trans hαu hx.1.le, le_trans hx.2.le hvβ⟩
    rw [← hpart.union] at hxI
    rcases hxI with (h | h) | h
    · exact absurd (le_csSup hbdd1 h) (not_le.mpr hx.1)
    · exact absurd (csInf_le hbdd2 h) (not_le.mpr hx.2)
    · exact h
  have ha3 : G v - G u ≤ ∫ t in Z₃, D t := by
    rw [← hSI Z₃ hmZ₃ hZ3sub]
    have := intervalIntegral_le_setIntegral (g := Dc) hDcI hDc0 (S := Z₃) huv hIoo
    rw [hGsub] at this; exact this
  -- chaining
  have hstep1 : c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t) ≤ c * (G u * (M - G v)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul ha1u ha2v ha2nn (le_trans ha1nn ha1u)) hc0
  have hstep2 : M * (G v - G u) ≤ M * ∫ t in Z₃, D t := by
    have hM0 : 0 ≤ M := by rw [hMeq]; exact hMnn
    exact mul_le_mul_of_nonneg_left ha3 hM0
  rw [← hMeq]
  linarith

/-- **`Arlib.oneDim_partition_of_side` with the two orientations combined.**

The conclusion, `hint` and `hcross` are all symmetric in `Z₁ ↔ Z₂`, so it is enough that the
two parts be *unmixed*: one of them lies weakly to the left of the other. -/
theorem oneDim_partition_of_unmixed (D : ℝ → ℝ) (Z₁ Z₂ Z₃ : Set ℝ) (κ : ℝ → ℝ → ℝ)
    (α β c : ℝ) (hαβ : α ≤ β) (hD0 : ∀ t ∈ Set.Icc α β, 0 ≤ D t)
    (hDint : IntervalIntegrable D volume α β)
    (hpart : IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃)
    (hmZ₁ : MeasurableSet Z₁) (hmZ₂ : MeasurableSet Z₂) (hmZ₃ : MeasurableSet Z₃)
    (hint : ∀ x y : ℝ, α ≤ x → x ≤ y → y ≤ β →
      κ x y * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
        ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t)
    (hcross : ∀ s ∈ Z₁, ∀ t ∈ Z₂, c ≤ κ (min s t) (max s t))
    (hside : (∀ s ∈ Z₁, ∀ t ∈ Z₂, s ≤ t) ∨ ∀ s ∈ Z₁, ∀ t ∈ Z₂, t ≤ s) :
    c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t) ≤ (∫ t in α..β, D t) * ∫ t in Z₃, D t := by
  rcases hside with hs | hs
  · exact oneDim_partition_of_side D Z₁ Z₂ Z₃ κ α β c hαβ hD0 hDint hpart hmZ₁ hmZ₂ hmZ₃
      hint hcross hs
  · have h := oneDim_partition_of_side D Z₂ Z₁ Z₃ κ α β c hαβ hD0 hDint hpart.symm hmZ₂ hmZ₁
      hmZ₃ hint (fun t ht s hs => by
        have h' := hcross s hs t ht
        rwa [min_comm, max_comm] at h') (fun s' hs' t' ht' => hs t' ht' s' hs')
    calc c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t)
        = c * ((∫ t in Z₂, D t) * ∫ t in Z₁, D t) := by ring
      _ ≤ (∫ t in α..β, D t) * ∫ t in Z₃, D t := h

end Reduction

/-! ### Non-vacuity, and the acid test against the recorded counterexample -/

section Witness

/-- Two disjoint subsets of `K`, together with what they leave over, form a three-way
partition of `K`. -/
theorem isPartition3_sdiff {E : Type*} {K Z₁ Z₂ : Set E} (h₁ : Z₁ ⊆ K) (h₂ : Z₂ ⊆ K)
    (hd : Disjoint Z₁ Z₂) : IsPartition3 K Z₁ Z₂ (K \ (Z₁ ∪ Z₂)) where
  union := Set.union_sdiff_cancel (Set.union_subset h₁ h₂)
  disjoint₁₂ := hd
  disjoint₁₃ := Set.disjoint_left.mpr fun _ hx hx' => hx'.2 (Or.inl hx)
  disjoint₂₃ := Set.disjoint_left.mpr fun _ hx hx' => hx'.2 (Or.inr hx)

/-- **The exact interval-case coefficient of the uniform weight on `[0,1]`.**

For the weight `D ≡ 1` the interval case reads `κ x y · x · (1−y) ≤ y − x`, so the largest
admissible coefficient is `(y − x)/(x(1 − y))`.  Mathlib's `a / 0 = 0` convention makes this
the value `0` at `x = 0` and at `y = 1`, where the interval case carries no information
anyway. -/
noncomputable def uniformCoeff (x y : ℝ) : ℝ := (y - x) / (x * (1 - y))

/-- `Arlib.uniformCoeff` satisfies the interval case for the uniform weight on `[0,1]`, with
equality wherever `x(1 − y) ≠ 0`. -/
theorem uniformCoeff_intervalCase (x y : ℝ) (hxy : x ≤ y) :
    uniformCoeff x y * ((∫ _t in (0:ℝ)..x, (1:ℝ)) * ∫ _t in y..(1:ℝ), (1:ℝ))
      ≤ (∫ _t in (0:ℝ)..(1:ℝ), (1:ℝ)) * ∫ _t in x..y, (1:ℝ) := by
  have e1 : (∫ _t in (0:ℝ)..x, (1:ℝ)) = x := by simp
  have e2 : (∫ _t in y..(1:ℝ), (1:ℝ)) = 1 - y := by simp
  have e3 : (∫ _t in (0:ℝ)..(1:ℝ), (1:ℝ)) = 1 := by simp
  have e4 : (∫ _t in x..y, (1:ℝ)) = y - x := by simp
  rw [e1, e2, e3, e4, one_mul, uniformCoeff]
  rcases eq_or_ne (x * (1 - y)) 0 with h | h
  · rw [h, mul_zero]; linarith
  · rw [div_mul_cancel₀ _ h]

/-- The integral of the constant weight `1` over a set of finite measure is its measure. -/
theorem setIntegral_one (S : Set ℝ) : (∫ _t in S, (1:ℝ)) = (volume S).toReal := by
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]

/-- **The acid test: the separation hypothesis excludes the recorded counterexample.**

`Arlib.Convexity.SharpIsoperimetry` records the configuration that refutes the literal
reading of `vol3_journal.tex:497`: `D ≡ 1` on `[0,1]`, `Z₁ = [0,0.4] ∪ [0.6,1]`,
`Z₂ = (0.45,0.5)` and `c = 4`.  It satisfies both post-localisation relations, yet no interval
reduction exists in either orientation.

If the separation hypothesis `hcross` did not exclude it, `Arlib.oneDim_partition_of_side`
would be false.  It does exclude it: the interval case at the cross pair `(0.4, 0.46)` — a
genuine cross pair, since `0.4 ∈ Z₁` and `0.46 ∈ Z₂` — pins `κ (0.4) (0.46) ≤ 5/18`, so
`hcross` forces `c ≤ 5/18`, well below the `c = 4` the counterexample needs.  No property of
`κ` beyond the interval case is used, so this holds for *every* coefficient function. -/
theorem cousinsVempala_counterexample_c_le (κ : ℝ → ℝ → ℝ) (c : ℝ)
    (hint : ∀ x y : ℝ, (0:ℝ) ≤ x → x ≤ y → y ≤ 1 →
      κ x y * ((∫ _t in (0:ℝ)..x, (1:ℝ)) * ∫ _t in y..(1:ℝ), (1:ℝ))
        ≤ (∫ _t in (0:ℝ)..(1:ℝ), (1:ℝ)) * ∫ _t in x..y, (1:ℝ))
    (hcross : ∀ s ∈ Set.Icc (0:ℝ) (2/5) ∪ Set.Icc (3/5) (1:ℝ),
      ∀ t ∈ Set.Ioo (9/20 : ℝ) (1/2), c ≤ κ (min s t) (max s t)) :
    c ≤ 5 / 18 := by
  have hs : (2/5 : ℝ) ∈ Set.Icc (0:ℝ) (2/5) ∪ Set.Icc (3/5) (1:ℝ) :=
    Or.inl ⟨by norm_num, le_rfl⟩
  have ht : (23/50 : ℝ) ∈ Set.Ioo (9/20 : ℝ) (1/2) := ⟨by norm_num, by norm_num⟩
  have h1 := hcross _ hs _ ht
  rw [min_eq_left (by norm_num : (2/5:ℝ) ≤ 23/50),
    max_eq_right (by norm_num : (2/5:ℝ) ≤ 23/50)] at h1
  have h2 := hint (2/5) (23/50) (by norm_num) (by norm_num) (by norm_num)
  have e1 : (∫ _t in (0:ℝ)..(2/5 : ℝ), (1:ℝ)) = 2/5 := by norm_num
  have e2 : (∫ _t in (23/50 : ℝ)..(1:ℝ), (1:ℝ)) = 27/50 := by norm_num
  have e3 : (∫ _t in (0:ℝ)..(1:ℝ), (1:ℝ)) = 1 := by norm_num
  have e4 : (∫ _t in (2/5 : ℝ)..(23/50 : ℝ), (1:ℝ)) = 3/50 := by norm_num
  rw [e1, e2, e3, e4] at h2
  linarith

/-- **Non-vacuity of `Arlib.oneDim_partition_of_side`.**

Every hypothesis of the theorem is satisfiable simultaneously, at data where the conclusion
is a *strictly positive* lower bound rather than the trivial `0 ≤ …`.  The instance is the
uniform weight on `[0,1]`, the coefficient `Arlib.uniformCoeff`,

  `Z₁ = [1/8, 1/4]`,  `Z₂ = (3/4, 7/8]`,  `Z₃` the rest,  `c = 8`,

for which `κ (min s t) (max s t) = (t − s)/(s(1 − t)) > 8` on every cross pair (the infimum
`8` is approached at `s = 1/4`, `t → 3/4⁺` and not attained), and
`c · (∫_{Z₁})(∫_{Z₂}) = 8 · (1/8)(1/8) = 1/8 > 0`. -/
theorem oneDim_partition_witness :
    ∃ (D : ℝ → ℝ) (Z₁ Z₂ Z₃ : Set ℝ) (κ : ℝ → ℝ → ℝ) (α β c : ℝ),
      α ≤ β ∧ (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ IntervalIntegrable D volume α β ∧
      IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃ ∧
      MeasurableSet Z₁ ∧ MeasurableSet Z₂ ∧ MeasurableSet Z₃ ∧
      (∀ x y : ℝ, α ≤ x → x ≤ y → y ≤ β →
        κ x y * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
          ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t) ∧
      (∀ s ∈ Z₁, ∀ t ∈ Z₂, c ≤ κ (min s t) (max s t)) ∧
      (∀ s ∈ Z₁, ∀ t ∈ Z₂, s ≤ t) ∧
      0 < c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t) := by
  refine ⟨fun _ => (1:ℝ), Set.Icc (1/8) (1/4), Set.Ioc (3/4) (7/8),
    Set.Icc 0 1 \ (Set.Icc (1/8) (1/4) ∪ Set.Ioc (3/4) (7/8)), uniformCoeff, 0, 1, 8,
    by norm_num, fun _ _ => zero_le_one, intervalIntegrable_const, ?_,
    measurableSet_Icc, measurableSet_Ioc,
    measurableSet_Icc.diff (measurableSet_Icc.union measurableSet_Ioc),
    fun x y _ hxy _ => uniformCoeff_intervalCase x y hxy, ?_,
    fun s hs t ht => le_trans hs.2 (le_of_lt (lt_trans (by norm_num) ht.1)), ?_⟩
  · exact isPartition3_sdiff (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (by linarith [hx'.1]))
  · -- separation on cross pairs
    intro s hs t ht
    have hst : s ≤ t := le_trans hs.2 (le_of_lt (lt_trans (by norm_num) ht.1))
    rw [min_eq_left hst, max_eq_right hst, uniformCoeff, le_div_iff₀ (by nlinarith [hs.1, ht.2])]
    nlinarith [hs.1, hs.2, ht.1, ht.2]
  · -- the left-hand side is strictly positive
    have h1 : (∫ _t in Set.Icc (1/8:ℝ) (1/4), (1:ℝ)) = 1/8 := by
      rw [setIntegral_one, Real.volume_Icc]
      norm_num
    have h2 : (∫ _t in Set.Ioc (3/4:ℝ) (7/8), (1:ℝ)) = 1/8 := by
      rw [setIntegral_one, Real.volume_Ioc]
      norm_num
    rw [h1, h2]
    norm_num

/-- **The one-sidedness hypothesis is a genuine restriction.**

`Arlib.oneDim_partition_of_side` is not `hcombinatorial`: it needs `hside`, and `hside` does
*not* follow from the remaining hypotheses.  Here is data satisfying every hypothesis of
`hcombinatorial` — the interval case, and separation with a strictly positive `c` — in which
`Z₁` lies on **both** sides of `Z₂`:

  `D ≡ 1` on `[0,1]`,  `Z₁ = [0.1,0.4] ∪ [0.6,0.9]`,  `Z₂ = (0.45,0.5)`,  `c = 5/22`.

The infimum of `(t − s)/(s(1 − t))` over the left cross pairs is `5/22`, approached at
`s = 0.4, t → 0.45⁺`; over the right cross pairs, where the roles of `min` and `max` are
exchanged, it is `(0.6 − 0.5)/(0.5 · 0.4) = 1/2 > 5/22`.  So separation alone does not
un-interleave a configuration, and the interleaved case of `hcombinatorial` is exactly what
this file leaves open.  (The conclusion does hold here — `c (∫_{Z₁})(∫_{Z₂}) = 3/440` against
`(∫_0^1)(∫_{Z₃}) = 7/20` — it is only the *proof* that is missing.) -/
theorem hside_not_implied :
    ∃ (D : ℝ → ℝ) (Z₁ Z₂ Z₃ : Set ℝ) (κ : ℝ → ℝ → ℝ) (α β c : ℝ),
      α ≤ β ∧ (∀ t ∈ Set.Icc α β, 0 ≤ D t) ∧ IntervalIntegrable D volume α β ∧
      IsPartition3 (Set.Icc α β) Z₁ Z₂ Z₃ ∧
      MeasurableSet Z₁ ∧ MeasurableSet Z₂ ∧ MeasurableSet Z₃ ∧
      (∀ x y : ℝ, α ≤ x → x ≤ y → y ≤ β →
        κ x y * ((∫ t in α..x, D t) * ∫ t in y..β, D t)
          ≤ (∫ t in α..β, D t) * ∫ t in x..y, D t) ∧
      (∀ s ∈ Z₁, ∀ t ∈ Z₂, c ≤ κ (min s t) (max s t)) ∧
      0 < c * ((∫ t in Z₁, D t) * ∫ t in Z₂, D t) ∧
      ¬((∀ s ∈ Z₁, ∀ t ∈ Z₂, s ≤ t) ∨ ∀ s ∈ Z₁, ∀ t ∈ Z₂, t ≤ s) := by
  refine ⟨fun _ => (1:ℝ), Set.Icc (1/10) (2/5) ∪ Set.Icc (3/5) (9/10),
    Set.Ioo (9/20) (1/2),
    Set.Icc 0 1 \ ((Set.Icc (1/10) (2/5) ∪ Set.Icc (3/5) (9/10)) ∪ Set.Ioo (9/20) (1/2)),
    uniformCoeff, 0, 1, 5/22,
    by norm_num, fun _ _ => zero_le_one, intervalIntegrable_const, ?_,
    (measurableSet_Icc.union measurableSet_Icc), measurableSet_Ioo,
    measurableSet_Icc.diff ((measurableSet_Icc.union measurableSet_Icc).union
      measurableSet_Ioo),
    fun x y _ hxy _ => uniformCoeff_intervalCase x y hxy, ?_, ?_, ?_⟩
  · refine isPartition3_sdiff ?_ (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) ?_
    · rintro x (hx | hx) <;> exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · refine Set.disjoint_left.mpr ?_
      rintro x (hx | hx) hx'
      · exact absurd hx.2 (by linarith [hx'.1])
      · exact absurd hx.1 (by linarith [hx'.2])
  · -- separation on cross pairs, in both orientations
    rintro s (hs | hs) t ht
    · have hst : s ≤ t := by linarith [hs.2, ht.1]
      rw [min_eq_left hst, max_eq_right hst, uniformCoeff,
        le_div_iff₀ (by nlinarith [hs.1, ht.2])]
      nlinarith [hs.1, hs.2, ht.1, ht.2]
    · have hts : t ≤ s := by linarith [hs.1, ht.2]
      rw [min_eq_right hts, max_eq_left hts, uniformCoeff,
        le_div_iff₀ (by nlinarith [ht.1, hs.2])]
      nlinarith [hs.1, hs.2, ht.1, ht.2]
  · -- the left-hand side is strictly positive
    have hdisj : Disjoint (Set.Icc (1/10:ℝ) (2/5)) (Set.Icc (3/5:ℝ) (9/10)) :=
      Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (by linarith [hx'.1])
    have h1 : (∫ _t in Set.Icc (1/10:ℝ) (2/5) ∪ Set.Icc (3/5:ℝ) (9/10), (1:ℝ)) = 3/5 := by
      rw [setIntegral_one, measure_union hdisj measurableSet_Icc, Real.volume_Icc,
        Real.volume_Icc, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    have h2 : (∫ _t in Set.Ioo (9/20:ℝ) (1/2), (1:ℝ)) = 1/20 := by
      rw [setIntegral_one, Real.volume_Ioo]
      norm_num
    rw [h1, h2]
    norm_num
  · -- `Z₁` lies on both sides of `Z₂`
    rintro (h | h)
    · have := h (9/10) (Or.inr ⟨by norm_num, le_rfl⟩) (23/50) ⟨by norm_num, by norm_num⟩
      linarith
    · have := h (1/10) (Or.inl ⟨le_rfl, by norm_num⟩) (23/50) ⟨by norm_num, by norm_num⟩
      linarith

end Witness

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.nonneg_csSup_csInf
#print axioms Arlib.setIntegral_le_intervalIntegral
#print axioms Arlib.intervalIntegral_le_setIntegral
#print axioms Arlib.oneDim_partition_of_side
#print axioms Arlib.oneDim_partition_of_unmixed
#print axioms Arlib.isPartition3_sdiff
#print axioms Arlib.uniformCoeff_intervalCase
#print axioms Arlib.setIntegral_one
#print axioms Arlib.cousinsVempala_counterexample_c_le
#print axioms Arlib.oneDim_partition_witness
#print axioms Arlib.hside_not_implied
