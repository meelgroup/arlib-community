/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoEnlargeContinuous
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoInnerRegular

/-!
# From *measurable* `S₁, S₂, S₃` to disjoint open enlargements, for a continuous density

This is the join of the two halves that precede it:

* `Arlib.exists_compact_subset_setIntegral_ge` (`Arlib/Convexity/IsoInnerRegular.lean`) —
  inner regularity: a measurable `S` contains a **compact** `C ⊆ S ∩ {h > 0}` carrying all
  but `ε` of `∫_S h`;
* `Arlib.exists_disjoint_open_enlargement_of_continuous`
  (`Arlib/Convexity/IsoEnlargeContinuous.lean`) — disjoint **open** enlargements of two
  disjoint compacts inside `{h > 0}`, at any strictly weakened thresholds, needing nothing of
  `h` but continuity.

Composing them gives exactly the hypothesis a slack-tolerant form of
`Arlib.gaussianRestricted_isoperimetry_of_openClosed_enlargement`
(`Arlib/Convexity/IsoOpenClosed.lean:1114`) consumes, in Cousins–Vempala's own threshold
shape `d/log 2` and `4(d/σ)√n`.

## Why this evades the known obstruction

`Arlib.exists_separated_no_disjoint_open_enlargement` (`IsoOpenClosed.lean:1205`) exhibits
data satisfying every hypothesis of `thm:iso` for which **no** disjoint open supersets of
`S₁, S₂` exist at all — the two sets touch, and they touch *inside* `{h = 0}`, where the
density branch of the disjunction is satisfied at distance `0`.

The composition here never asks for supersets of `S₁, S₂`. It asks for supersets of compact
subsets of `S₁ ∩ {h > 0}` and `S₂ ∩ {h > 0}`, which are disjoint **compact** sets and hence a
positive distance apart. The mass discarded is `≤ ε` on each side, because `h` vanishes on
`{h = 0}`; and the residual set `(U₁ ∪ U₂)ᶜ` therefore exceeds `S₃` by at most `2ε`. That is
the `2ε` in the statement below, and it is why the conclusion is stated with slack rather
than exactly.

## What is proved here

* `Arlib.exists_enlargement_of_measurable` — the composition, in the `∃ U₁ U₂, …` shape.
* `Arlib.exists_enlargement_of_measurable_witness` — non-vacuity.

## Scope

Still not an isoperimetric inequality: the remaining step is to feed this to the open/closed
capstone and pass to the limit `ε ↓ 0`, `d' ↑ d`. Nothing here may be quoted as a
conductance, mixing-time or runtime statement.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib

open MeasureTheory Metric

variable {n : ℕ}

/-! ## 1. Monotonicity of the set integral of a nonnegative integrable function -/

/-- Set-monotonicity of `∫_A h` for `h ≥ 0` integrable.  Used four times below. -/
theorem setIntegral_mono_set_of_nonneg {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh0 : ∀ x, 0 ≤ h x) (hhi : Integrable h)
    {A B : Set (EuclideanSpace ℝ (Fin n))} (hAB : A ⊆ B) :
    ∫ x in A, h x ≤ ∫ x in B, h x :=
  setIntegral_mono_set hhi.integrableOn (Filter.Eventually.of_forall fun x => hh0 x)
    (HasSubset.Subset.eventuallyLE hAB)

/-- The mass of `S` outside a compact `C ⊆ S` that already carries all but `ε`. -/
theorem setIntegral_sdiff_le_of_compact_ge {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hhi : Integrable h) {S C : Set (EuclideanSpace ℝ (Fin n))} (hC : MeasurableSet C)
    (hCS : C ⊆ S) {ε : ℝ} (hint : ∫ x in S, h x ≤ (∫ x in C, h x) + ε) :
    ∫ x in S \ C, h x ≤ ε := by
  have hsplit : (∫ x in S ∩ C, h x) + ∫ x in S \ C, h x = ∫ x in S, h x :=
    integral_inter_add_sdiff hC hhi.integrableOn
  rw [Set.inter_eq_self_of_subset_right hCS] at hsplit
  linarith

/-! ## 2. The composition -/

/-- **Measurable `S₁, S₂, S₃` admit disjoint open enlargements with `ε`-slack, at any
strictly smaller separation parameter — for any continuous nonnegative integrable `h`.**

No hypothesis on `h` beyond continuity, nonnegativity and integrability: no Lipschitz
constant, no bound relating `σ`, `R` and `n`, no dimension threshold.  `n ≠ 0` is used only
to know `√n > 0`, so that the density threshold `4(d/σ)√n` is strictly monotone in `d`.

The three mass clauses are exactly what a slack-tolerant reduction needs:

* `U₁` carries all but `ε` of `S₁`'s mass, and likewise `U₂` for `S₂`;
* the residual `(U₁ ∪ U₂)ᶜ` carries at most `S₃`'s mass plus `2ε` — one `ε` for each of the
  two pieces of `S₁, S₂` that the compacts failed to capture. -/
theorem exists_enlargement_of_measurable (hn : n ≠ 0) {σ d d' ε : ℝ}
    (hσ : 0 < σ) (hd'd : d' < d) (hε : 0 < ε)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hhc : Continuous h) (hh0 : ∀ x, 0 ≤ h x)
    (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
      ((∫ x in S₁, h x) - ε ≤ ∫ x in U₁, h x) ∧
      ((∫ x in S₂, h x) - ε ≤ ∫ x in U₂, h x) ∧
      ((∫ x in (U₁ ∪ U₂)ᶜ, h x) ≤ (∫ x in S₃, h x) + 2 * ε) ∧
      (∀ u ∈ U₁, ∀ v ∈ U₂,
        d' / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d' / σ) * Real.sqrt n ≤ densDist h u v) := by
  classical
  -- inner regularity on each side, inside `{h > 0}`
  obtain ⟨C₁, hC₁c, hC₁S, hC₁pos, hC₁int⟩ :=
    exists_compact_subset_setIntegral_ge hhc hh0 hhi hS₁ hε
  obtain ⟨C₂, hC₂c, hC₂S, hC₂pos, hC₂int⟩ :=
    exists_compact_subset_setIntegral_ge hhc hh0 hhi hS₂ hε
  have hCdisj : Disjoint C₁ C₂ := hpart.disjoint₁₂.mono hC₁S hC₂S
  -- both thresholds are strictly monotone in `d`
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hlt₁ : d' / Real.log 2 < d / Real.log 2 := by gcongr
  have hlt₂ : 4 * (d' / σ) * Real.sqrt n < 4 * (d / σ) * Real.sqrt n := by
    have hdiv : d' / σ < d / σ := by gcongr
    nlinarith [hsqrt, hdiv]
  -- the enlargement
  obtain ⟨U₁, U₂, hU₁o, hU₂o, hUd, hCU₁, hCU₂, hUsep⟩ :=
    exists_disjoint_open_enlargement_of_continuous hhc hC₁c hC₂c hC₁pos hC₂pos hCdisj hlt₁ hlt₂
      (fun u hu v hv => hsep u (hC₁S hu) v (hC₂S hv))
  refine ⟨U₁, U₂, hU₁o, hU₂o, hUd, ?_, ?_, ?_, hUsep⟩
  · have := setIntegral_mono_set_of_nonneg hh0 hhi hCU₁
    linarith
  · have := setIntegral_mono_set_of_nonneg hh0 hhi hCU₂
    linarith
  · -- the residual, cut along the partition
    have hUm : MeasurableSet (U₁ ∪ U₂) := (hU₁o.union hU₂o).measurableSet
    have hUcm : MeasurableSet (U₁ ∪ U₂)ᶜ := hUm.compl
    set T₁ : Set (EuclideanSpace ℝ (Fin n)) := (U₁ ∪ U₂)ᶜ ∩ S₁ with hT₁def
    set T₂ : Set (EuclideanSpace ℝ (Fin n)) := (U₁ ∪ U₂)ᶜ ∩ S₂ with hT₂def
    set T₃ : Set (EuclideanSpace ℝ (Fin n)) := (U₁ ∪ U₂)ᶜ ∩ S₃ with hT₃def
    have hT₁m : MeasurableSet T₁ := hUcm.inter hS₁
    have hT₂m : MeasurableSet T₂ := hUcm.inter hS₂
    have hT₃m : MeasurableSet T₃ := hUcm.inter hS₃
    -- the three pieces cover the residual, because `S₁, S₂, S₃` cover everything
    have hcover : (U₁ ∪ U₂)ᶜ = (T₁ ∪ T₂) ∪ T₃ := by
      rw [hT₁def, hT₂def, hT₃def, ← Set.inter_union_distrib_left,
        ← Set.inter_union_distrib_left, hpart.union, Set.inter_univ]
    -- and they are pairwise disjoint, because `S₁, S₂, S₃` are
    have hd₁₂ : Disjoint T₁ T₂ :=
      hpart.disjoint₁₂.mono Set.inter_subset_right Set.inter_subset_right
    have hd₁₃ : Disjoint T₁ T₃ :=
      hpart.disjoint₁₃.mono Set.inter_subset_right Set.inter_subset_right
    have hd₂₃ : Disjoint T₂ T₃ :=
      hpart.disjoint₂₃.mono Set.inter_subset_right Set.inter_subset_right
    have hsplit : ∫ x in (U₁ ∪ U₂)ᶜ, h x
        = ((∫ x in T₁, h x) + ∫ x in T₂, h x) + ∫ x in T₃, h x := by
      rw [hcover, setIntegral_union (Set.disjoint_union_left.mpr ⟨hd₁₃, hd₂₃⟩) hT₃m
        hhi.integrableOn hhi.integrableOn,
        setIntegral_union hd₁₂ hT₂m hhi.integrableOn hhi.integrableOn]
    -- `T₁` misses `C₁` entirely, so it lies in the `ε`-small part of `S₁`
    have hT₁sub : T₁ ⊆ S₁ \ C₁ := by
      intro x hx
      refine ⟨hx.2, fun hc => hx.1 (Set.mem_union_left _ (hCU₁ hc))⟩
    have hT₂sub : T₂ ⊆ S₂ \ C₂ := by
      intro x hx
      refine ⟨hx.2, fun hc => hx.1 (Set.mem_union_right _ (hCU₂ hc))⟩
    have hb₁ : ∫ x in T₁, h x ≤ ε :=
      le_trans (setIntegral_mono_set_of_nonneg hh0 hhi hT₁sub)
        (setIntegral_sdiff_le_of_compact_ge hhi hC₁c.measurableSet hC₁S hC₁int)
    have hb₂ : ∫ x in T₂, h x ≤ ε :=
      le_trans (setIntegral_mono_set_of_nonneg hh0 hhi hT₂sub)
        (setIntegral_sdiff_le_of_compact_ge hhi hC₂c.measurableSet hC₂S hC₂int)
    have hb₃ : ∫ x in T₃, h x ≤ ∫ x in S₃, h x :=
      setIntegral_mono_set_of_nonneg hh0 hhi Set.inter_subset_right
    rw [hsplit]
    linarith

/-! ## 3. Non-vacuity (`CLAUDE.md` §11) -/

/-- **The hypothesis bundle of `Arlib.exists_enlargement_of_measurable` is satisfiable, with
`S₁` and `S₂` both of positive `h`-mass.**

`n = 1`, `h x = max 0 (5 − ‖x‖)` (continuous, nonnegative, compactly supported hence
integrable), `S₁ = closedBall 0 (1/2)`, `S₂ = {x | 3 ≤ ‖x‖}`, `S₃` the rest, `σ = 1`, `d = 1`,
`d' = 1/2`, `ε = 1`.  The separation holds on the metric branch, `‖u − v‖ ≥ 5/2 > 1/log 2`.

Both `S₁ ∩ {h > 0}` and `S₂ ∩ {h > 0}` are nonempty here — `h = 5` at the centre and `h = 2`
on `{‖x‖ = 3}` — so inner regularity returns nonempty compacts and the theorem does not
reduce to the degenerate branches of
`Arlib.exists_disjoint_open_enlargement_of_continuous`.

For an instance where the **density** branch carries the disjunction on its own, see
`Arlib.exists_disjoint_open_enlargement_of_continuous_witness`. -/
theorem exists_enlargement_of_measurable_witness :
    ∃ (k : ℕ) (h : EuclideanSpace ℝ (Fin k) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin k))) (σ d d' ε : ℝ),
      k ≠ 0 ∧ 0 < σ ∧ d' < d ∧ 0 < ε ∧
      Continuous h ∧ (∀ x, 0 ≤ h x) ∧ Integrable h ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (∃ x ∈ S₁, 0 < h x) ∧ (∃ x ∈ S₂, 0 < h x) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt k ≤ densDist h u v) := by
  classical
  set h : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => max 0 (5 - ‖x‖) with hhdef
  have hcont : Continuous h := by rw [hhdef]; fun_prop
  have hh0 : ∀ x, 0 ≤ h x := fun x => le_max_left _ _
  have hsupp : ∀ x : EuclideanSpace ℝ (Fin 1), x ∉ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 5 →
      h x = 0 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    rw [hhdef]
    exact max_eq_left (by linarith)
  have hint : Integrable h :=
    hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 1)) 5) hsupp)
  set S₁ : Set (EuclideanSpace ℝ (Fin 1)) := closedBall 0 (1 / 2) with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin 1)) := {x | 3 ≤ ‖x‖} with hS₂def
  have hmem₁ : ∀ x : EuclideanSpace ℝ (Fin 1), x ∈ S₁ ↔ ‖x‖ ≤ 1 / 2 := by
    intro x; rw [hS₁def, mem_closedBall, dist_zero_right]
  have hS₁m : MeasurableSet S₁ := measurableSet_closedBall
  have hS₂m : MeasurableSet S₂ :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hdisj₁₂ : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have h1 := (hmem₁ x).1 hx₁
    have h2 : (3 : ℝ) ≤ ‖x‖ := hx₂
    linarith
  refine ⟨1, h, S₁, S₂, (S₁ ∪ S₂)ᶜ, 1, 1, 1 / 2, 1, one_ne_zero, one_pos, by norm_num,
    one_pos, hcont, hh0, hint,
    { union := Set.union_compl_self _
      disjoint₁₂ := hdisj₁₂
      disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
      disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) },
    hS₁m, hS₂m, (hS₁m.union hS₂m).compl, ?_, ?_, ?_⟩
  · refine ⟨0, (hmem₁ 0).2 (by simp), ?_⟩
    rw [hhdef]
    simp
  · refine ⟨EuclideanSpace.single ⟨0, by omega⟩ (3 : ℝ), ?_, ?_⟩
    · show (3 : ℝ) ≤ ‖_‖
      rw [PiLp.norm_single]
      norm_num
    · rw [hhdef]
      simp only [PiLp.norm_single]
      norm_num
  · intro u hu v hv
    left
    have h1 : ‖u‖ ≤ 1 / 2 := (hmem₁ u).1 hu
    have h2 : (3 : ℝ) ≤ ‖v‖ := hv
    -- `log 2 ≥ 1/2`, from `log x ≤ x − 1` at `x = 1/2`
    have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have hx := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num)
      rw [Real.log_inv] at hx
      norm_num at hx
      linarith
    have hlogpos : 0 < Real.log 2 := by linarith
    have huv : (5 : ℝ) / 2 ≤ ‖u - v‖ := by
      have := norm_sub_norm_le v u
      rw [norm_sub_rev v u] at this
      linarith
    have hdiv : (1 : ℝ) / Real.log 2 ≤ 5 / 2 := by
      rw [div_le_div_iff₀ hlogpos (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith

section AxiomCheck

#print axioms Arlib.setIntegral_mono_set_of_nonneg
#print axioms Arlib.exists_enlargement_of_measurable_witness
#print axioms Arlib.setIntegral_sdiff_le_of_compact_ge
#print axioms Arlib.exists_enlargement_of_measurable

end AxiomCheck

end Arlib
