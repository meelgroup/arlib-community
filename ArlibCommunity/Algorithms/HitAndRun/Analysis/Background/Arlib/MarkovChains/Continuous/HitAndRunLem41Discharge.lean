/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunUncond

/-!
# Lemma 4.1 discharged, and Theorem 4.2 with `hLem41` gone

`Arlib.MarkovChains.tvLe_hitAndRun_lemma41_uncond` (`SphereCap.lean`) proves Lovász–Vempala's
Lemma 4.1 with no unproved hypothesis, at overlap constant `1 − 1/8000`, for `n ≥ 1100`.  It
was nevertheless unusable as a discharge of the `hLem41` binder of Theorem 4.2, because it
carries three side conditions that the binder does not:

* `hmoveu`, `hmovev` — `hitAndRunProposal K u Set.univ = 1`;
* `ha` — `chordLow K u v < 0`;
* `hb` — `1 < chordHigh K u v`.

**`ha` is not merely inconvenient at the boundary; it is false there.**  For `u ∈ K` outside
`interior K` and `v ∈ interior K`, a point `u + t(v − u) ∈ K` with `t < 0` would put `u` on an
open segment between a point of `K` and an interior point of `K`, hence in `interior K`.  So
`chordLow K u v = 0` for every such pair, in every body, in every dimension — proved below as
`Arlib.MarkovChains.chordLow_eq_zero_of_notMem_interior`.  As long as the `hLem41` binder is
stated over all of `K`, no route through `tvLe_hitAndRun_lemma41_uncond` can close it, and a
theorem asserting `∀ u ∈ K, ∀ v ∈ K, u ≠ v → chordLow K u v < 0` would be vacuous.

The resolution is that Theorem 4.2's proof never needed the binder over all of `K`: it cuts
`S₁'` and `S₂'` down to `interior K` (`HitAndRunConductance.lean`, module docstring, § *Two
places where the formalisation is more careful than the paper*, item 1) and applies `hLem41`
only at interior points.  `Arlib.MarkovChains.conductance_hitAndRun_ge_of_tv_interior` is that
theorem with the binder weakened accordingly — a strictly weaker hypothesis, as the derivation
of the unchanged `conductance_hitAndRun_ge_of_tv` from it witnesses.  On `interior K` all three
side conditions are available:

| side condition | source |
|---|---|
| `hmove` | `Arlib.hitAndRunProposal_univ_eq_one_of_mem_interior` |
| `ha` | `Arlib.chordLow_neg_of_mem_interior` |
| `hb` | `Arlib.one_lt_chordHigh_of_mem_interior` |
| `max (medianStep K u) (medianStep K v)` versus `medianStep K u` | `Arlib.MarkovChains.tvLe_hitAndRun_lemma41_uncond_max` |
| `u ≠ v` | case split; `Arlib.TVLe.refl` and `Arlib.TVLe.mono` on the diagonal |

## What is here

| name | content |
|---|---|
| `hLem41_interior_uncond` | **Lemma 4.1 as the interior binder, proved**: `∀ u ∈ interior K, ∀ v ∈ interior K, …` at `1 − 1/8000`, `n ≥ 1100`, no unproved hypothesis |
| `conductance_hitAndRun_ge_uncond_lem41` | Theorem 4.2 with `hLem41` **gone**: `Φ ≥ (1/8000)/(245760·n·D)`, only the isoperimetry binder left |
| `conductance_hitAndRun_ge_uncond_lem41_pow` | the same, rounded to `Φ ≥ 1/(2³¹·n·D)` |
| `chordLow_eq_zero_of_notMem_interior` | the boundary obstruction, proved: `chordLow K u v = 0` for `u ∈ K \ interior K`, `v ∈ interior K` |

## Constants

`1966080000 = 8000 · 245760`, and `1966080000 ≤ 2³¹ = 2147483648`.  The paper's Theorem 4.2
reads `Φ ≥ 1/(2²⁴·n·D)`; the `2³¹` here is `2²⁴` times `8000/500 = 16` (Lemma 4.1's corrected
constant, `HitAndRunOverlap.lean`) times a further `8` from the factor `10` in the proved
Lemma 3.3 and the rounding to a power of two.  The order `1/(n·D)` is the paper's.

## What remains in Theorem 4.2

Only `hIso`, the paper's Theorem 2.1 (weighted isoperimetry) in the corrected form carrying
`∀ x ∈ K, h x ≤ 1/3`, without which it is false (`Arlib.not_hIso_two`).  Nothing here touches
it, and nothing here assumes it: it is passed through verbatim.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. Lemma 4.1 on the interior, with no unproved hypothesis -/

/-- **Lovász–Vempala's Lemma 4.1, in exactly the shape the (interior-ised) `hLem41` binder of
Theorem 4.2 asks for, proved.**

For `n ≥ 1100` and a convex, closed, measurable, bounded `K`: any two points of `interior K`
at cross-ratio distance `< 1/8` whose separation is `< (2/√n)·max(F u, F v)` have one-step
hit-and-run laws within total variation `1 − 1/8000`.

Every hypothesis of `Arlib.MarkovChains.tvLe_hitAndRun_lemma41_uncond_max` beyond the two the
binder supplies is discharged here, and each of them is exactly what needs the interior:
`hitAndRunProposal K u univ = 1` from `Arlib.hitAndRunProposal_univ_eq_one_of_mem_interior`,
`chordLow K u v < 0` from `Arlib.chordLow_neg_of_mem_interior`, and `1 < chordHigh K u v` from
`Arlib.one_lt_chordHigh_of_mem_interior`.  The diagonal `u = v` is not excluded by the binder
and is handled separately, by reflexivity.

This is a *statement about all interior pairs*, not a binder: it has no hypothesis that the
caller must supply beyond the geometry of `K` and `1100 ≤ n`. -/
theorem hLem41_interior_uncond (hn : 21 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) :
    ∀ u ∈ interior K, ∀ v ∈ interior K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 8000)) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  -- the walk leaves every interior point with probability one
  have hmove : ∀ x ∈ interior K, hitAndRunProposal K x Set.univ = 1 := by
    intro x hx
    obtain ⟨ε, hε, hbx⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    exact hitAndRunProposal_univ_eq_one_of_mem_interior hKm hε (hbx.trans interior_subset) hR
  intro u hu v hv hdK hF
  rcases eq_or_ne u v with rfl | huv
  · exact (Arlib.TVLe.refl _).mono bot_le
  exact tvLe_hitAndRun_lemma41_uncond_max hn hKc hKcl hKm hKb (interior_subset hu)
    (interior_subset hv) huv (hmove u hu) (hmove v hv)
    (chordLow_neg_of_mem_interior hKb huv hu) (one_lt_chordHigh_of_mem_interior hKb huv hv)
    hdK hF

/-! ## 2. Theorem 4.2 with `hLem41` gone -/

/-- **Theorem 4.2 of Lovász–Vempala with the Lemma 4.1 binder discharged.**

    Φ(hit-and-run on K)  ≥  (1/8000) / (245760 · n · D).

`Arlib.MarkovChains.conductance_hitAndRun_ge_of_tv_interior` at `lam = 1/8000`, with its
`hLem41` supplied by `hLem41_interior_uncond` rather than assumed.  The only mathematical
hypothesis left is `hIso`, the corrected Theorem 2.1, carried through verbatim.

Not routed through `Arlib.MarkovChains.conductance_hitAndRun_ge_param`: that theorem states
its `hLem41` over all of `K`, which is the form the boundary refutes
(`chordLow_eq_zero_of_notMem_interior` below).  The conclusion is the one `_param` would give
at `c = 1/8000`. -/
theorem conductance_hitAndRun_ge_uncond_lem41 (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (1 / 8000 / (245760 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_tv_interior (by omega) hKc hKcl hKm hKb hball hD
    (by norm_num) (by norm_num) (hLem41_interior_uncond hn hKc hKcl hKm hKb) hIso

/-- **The same bound, rounded to a power of two**: `Φ ≥ 1/(2³¹·n·D)`.

`8000 · 245760 = 1966080000 ≤ 2³¹ = 2147483648`.  Purely for legibility, in the style of
`Arlib.MarkovChains.conductance_hitAndRun_ge`'s `2²⁷`; the exact form
`conductance_hitAndRun_ge_uncond_lem41` is strictly stronger. -/
theorem conductance_hitAndRun_ge_uncond_lem41_pow (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (1 / (2 ^ 31 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn1 hKb hball) hD
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (conductance_hitAndRun_ge_uncond_lem41 hn hKc hKcl hKm hKb hball hD hIso)
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## 3. Why the `∀ u ∈ K` form is not available -/

/-- **The chord does not extend past a boundary point.**

For `K` convex, closed and bounded, `u ∈ K \ interior K` and `v ∈ interior K` with `u ≠ v`,

    chordLow K u v = 0,

so the hypothesis `ha : chordLow K u v < 0` of
`Arlib.MarkovChains.tvLe_hitAndRun_lemma41_uncond` fails at every such pair.  This is why the
`∀ u ∈ K, ∀ v ∈ K` form of the `hLem41` binder cannot be discharged through that route, and
why `hLem41_interior_uncond` is stated on `interior K`.

The argument: `chordLow ≤ 0` always (`Arlib.chordLow_nonpos`).  Were it `< 0`, the chord
parameter set — an interval, by `Arlib.chordParam_eq_Icc` — would contain that negative value
`s`, i.e. `w = u + s(v − u) ∈ K`.  Then `u` is the combination
`(−s/(1−s))·v + (1/(1−s))·w` with a strictly positive weight on the interior point `v`, so
`Convex.combo_interior_closure_mem_interior` puts `u` in `interior K`. -/
theorem chordLow_eq_zero_of_notMem_interior {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {u v : EuclideanSpace ℝ (Fin n)} (huv : u ≠ v) (hu : u ∈ K) (hu' : u ∉ interior K)
    (hv : v ∈ interior K) : chordLow K u v = 0 := by
  refine le_antisymm (chordLow_nonpos hKb huv hu) (not_lt.mp fun hlt => hu' ?_)
  set s : ℝ := chordLow K u v with hsdef
  -- the chord parameter set is `Icc (chordLow) (chordHigh)`, so `s` itself is a parameter
  have hsmem : s ∈ chordParam K u v := by
    rw [chordParam_eq_Icc hKc hKcl hKb huv hu]
    exact ⟨le_rfl, chordLow_le_chordHigh hKb huv hu (interior_subset hv)⟩
  set w : EuclideanSpace ℝ (Fin n) := (AffineMap.lineMap u v : ℝ → _) s with hwdef
  have hwK : w ∈ K := hsmem
  have hs1 : (0 : ℝ) < 1 - s := by linarith
  have hs1' : (1 : ℝ) - s ≠ 0 := hs1.ne'
  set a : ℝ := -s / (1 - s) with hadef
  set b : ℝ := 1 / (1 - s) with hbdef
  have ha0 : 0 < a := by rw [hadef]; exact div_pos (by linarith) hs1
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hab : a + b = 1 := by rw [hadef, hbdef]; field_simp; ring
  have hcombo : a • v + b • w = u := by
    rw [hwdef, Arlib.lineMap_apply']
    rw [hadef, hbdef]
    match_scalars <;> field_simp <;> ring
  have := hKc.combo_interior_closure_mem_interior hv (subset_closure hwK) ha0 hb0 hab
  rwa [hcombo] at this

/-! ## Axiom profile -/

section AxiomCheck

#print axioms hLem41_interior_uncond
#print axioms conductance_hitAndRun_ge_uncond_lem41
#print axioms conductance_hitAndRun_ge_uncond_lem41_pow
#print axioms chordLow_eq_zero_of_notMem_interior

end AxiomCheck

end Arlib.MarkovChains
