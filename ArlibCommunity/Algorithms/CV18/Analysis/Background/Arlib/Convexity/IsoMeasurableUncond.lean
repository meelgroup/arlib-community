/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoEnlargeMeasurable
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoEnlargeSlack
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.EllGaussianFacts
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.EllLogConcave

/-!
# Cousins–Vempala's `thm:iso` for **measurable** sets, with no Lipschitz hypothesis

`1409.6011/vol3_journal.tex:467` states `thm:iso` for an *arbitrary* partition `S₁, S₂, S₃`
of `ℝⁿ`.  Its proof reduces to the one-dimensional inequalities `(1d-1)`, `(1d-2)` by the
Localization Lemma, via the step at `vol3_journal.tex:499`:

> "By a standard combinatorial argument, we can assume that `Zᵢ = {t : (1−t)a+tb ∈ Sᵢ}` are
> intervals that partition `[a,b]`."

That step is not proved in the paper.  This repository proved the theorem for `S₁, S₂` **open**
and `S₃` **closed** — `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`
(`Arlib/Convexity/OneDimSharp.lean:631`), where the reduction *is* available — and the
measurable case has been the open blocker since.

**This file closes it.**  The composition is:

1. `Arlib.exists_enlargement_of_measurable` (`Arlib/Convexity/IsoEnlargeMeasurable.lean`) —
   inner regularity inside `{h > 0}` followed by
   `Arlib.exists_disjoint_open_enlargement_of_continuous`
   (`Arlib/Convexity/IsoEnlargeContinuous.lean`), giving disjoint **open** `U₁, U₂` that carry
   all but `ε` of the mass of `S₁, S₂` and satisfy the separation at any `d' < d`;
2. `Arlib.gaussianRestricted_isoperimetry_measurable_of_enlargements`
   (`Arlib/Convexity/IsoEnlargeSlack.lean`) — the open/closed capstone applied to
   `U₁, U₂, (U₁ ∪ U₂)ᶜ`, then `ε ↓ 0` and `d' ↑ d`.

## The two things that make it work

**Nothing is asked of `h` beyond continuity.**  The previous route to the measurable case —
`Arlib.exists_disjoint_open_enlargement_gaussianIndicator`
(`Arlib/Convexity/IsoIndicator.lean:405`) — discharges the *density* branch of the
disjunction by converting it into the *metric* branch, which needs a global log-Lipschitz
bound on `h`.  That is free for the indicator density `1_K·γ` and is the binder `hellLip` for
the `ℓ`-weighted one, where `AUDIT.md` §0i argues it has no witness with non-constant `ℓ`.
Here each pair stays in its own branch and only the *thresholds* move, so the estimate needed
is a perturbation bound for `densDist`, which uniform continuity on a compact set supplies —
**with the radius chosen after the sets**, hence with no inequality to satisfy against `σ`,
`R` or `n`.

**The known obstruction is evaded, not contradicted.**
`Arlib.exists_separated_no_disjoint_open_enlargement` (`Arlib/Convexity/IsoOpenClosed.lean:1205`)
exhibits data satisfying every hypothesis of `thm:iso` for which no disjoint open supersets of
`S₁, S₂` exist at all.  There the two sets touch, and they touch *inside* `{h = 0}`.  The route
above never asks for supersets of `S₁, S₂`: it asks for supersets of compact subsets of
`S₁ ∩ {h > 0}` and `S₂ ∩ {h > 0}`, which are disjoint compacts and hence a positive distance
apart, and the discarded part carries no mass precisely because `h` vanishes on it.

## What is proved here

* `Arlib.gaussianRestricted_isoperimetry_measurable_logTwo` — `thm:iso` at the separation
  threshold `d/log 2`, for **measurable** `S₁, S₂, S₃`, for `h = f·γ` with `f` an arbitrary
  nonnegative log-concave function and `h` continuous, bounded and integrable.

Every binder is one the open/closed capstone already had, except that `hS₁ : IsOpen S₁`,
`hS₂ : IsOpen S₂`, `hS₃ : IsClosed S₃` are replaced by `MeasurableSet`, and `hd : 0 < d` is
added (the `d ≤ 0` case is trivial but is not routed here).

## Scope

This is an isoperimetric inequality.  It is **not** a conductance bound, a mixing time or a
running time, and may not be quoted as one.  What it does supply is the `hiso` binder shape of
`Arlib.MarkovChains.conductance_speedyGaussian_ge`, once instantiated at a density; that
instantiation is a separate step and is not performed here.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib

open MeasureTheory

variable {n : ℕ}

/-- **Cousins–Vempala's `thm:iso` (`1409.6011/vol3_journal.tex:467`) for measurable
`S₁, S₂, S₃`, at the separation threshold `d/log 2`.**

This is `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo`
(`Arlib/Convexity/OneDimSharp.lean:631`) with its three regularity binders

    hS₁ : IsOpen S₁,  hS₂ : IsOpen S₂,  hS₃ : IsClosed S₃

replaced by `MeasurableSet S₁`, `MeasurableSet S₂`, `MeasurableSet S₃`.  Everything else —
`hf₀`, `hfc`, `hh`, `hhc`, `hhB`, `hhi`, `hpart`, `hmass`, `hsep` and the conclusion — is
verbatim, save the added `hd : 0 < d`.

The proof carries **no** Lipschitz hypothesis on `h`, and no relation between `σ`, `R` and
`n`; see the module docstring for why the route avoids one and why
`Arlib.exists_separated_no_disjoint_open_enlargement` does not apply to it. -/
theorem gaussianRestricted_isoperimetry_measurable_logTwo (hn : 2 ≤ n) {σ d B : ℝ}
    (hσ : 0 < σ) (hd : 0 < d)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₀ : ∀ x, 0 ≤ f x) (hfc : IsLogConcave f)
    (hh : ∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    (hhc : Continuous h) (hhB : ∀ x, h x ≤ B) (hhi : Integrable h)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hmass : 0 < ∫ x, h x)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  have hh0 : ∀ x, 0 ≤ h x := fun x => by
    rw [hh]; exact mul_nonneg (hf₀ x) (Real.exp_pos _).le
  refine gaussianRestricted_isoperimetry_measurable_of_enlargements hn hσ hd hf₀ hfc hh hhc
    hhB hhi hmass ?_
  intro ε hε d' _ hd'd
  exact exists_enlargement_of_measurable (by omega) hσ hd'd hε hhc hh0 hhi hpart hS₁ hS₂ hS₃ hsep

/-! ## The `ℓ`-weighted instantiation -/

/-- **`thm:iso` for measurable `S₁, S₂, S₃`, at the `ℓ`-weighted Gaussian density
`h = ℓ·γ` — with no Lipschitz hypothesis.**

This is `Arlib.ellGaussian_isoperimetry_openClosed_logTwo`
(`Arlib/Convexity/EllLogConcave.lean:474`) with `IsOpen S₁`, `IsOpen S₂`, `IsClosed S₃`
replaced by `MeasurableSet`.

Compare `Arlib.ellGaussian_isoperimetry_measurable_logTwo`
(`Arlib/Convexity/IsoWeighted.lean:851`), which reaches the measurable case through the
metric-enlargement detour and therefore carries

    hellLip : ∀ u ∈ K, ∀ v ∈ K, ℓ(u) ≤ ℓ(v)·exp(Lf·‖u − v‖)
    hLσ     : √3·(σ²·Lf + R) ≤ 2σ√n

which `AUDIT.md` §0i(b) argues admit no witness with non-constant `ℓ` at the operative step.
**Both are gone here**, together with `R` and `Lf` themselves.  The log-concavity of `ℓ`
(`Arlib.isLogConcave_ell_toReal`) does all the work that log-Lipschitzness was being asked
for, because the route never converts the density branch into the metric branch.

⚠ **This is still not the consumer's density.**  `hiso` in
`Arlib.MarkovChains.conductance_speedyGaussian_ge` is pinned by
`Arlib.MarkovChains.hpi_ellGaussian` to the **indicator** density `1_K·ℓ·γ`, which is
discontinuous across `∂K` and so fails `hhc`.  Bridging to it needs the mollification
argument that `Arlib.gaussianIndicator_isoperimetry_measurable`
(`Arlib/Convexity/IsoIndicator.lean:476`) performs for `1_K·γ`, carried out with the extra
factor `ℓ`.  Until that lands, nothing here may be quoted as a conductance, mixing-time or
runtime bound.  See `AUDIT.md` §0j. -/
theorem ellGaussian_isoperimetry_measurable_logTwo_uncond (hn : 2 ≤ n) {σ d δ : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (hδ : 0 < δ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = (MarkovChains.ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x :=
  gaussianRestricted_isoperimetry_measurable_logTwo hn hσ hd
    (fun _ => ENNReal.toReal_nonneg) (isLogConcave_ell_toReal hK hKc δ) hh
    (ellGaussian_continuous (by omega) hδ.le hh)
    (ellGaussian_le_one hh)
    (ellGaussian_integrable (by omega) hδ.le hσ hh)
    hpart hS₁ hS₂ hS₃
    (ellGaussian_integral_pos (by omega) hδ hσ hKc hKb hK0 hh)
    hsep

/-! ## Non-vacuity of the capstone (`CLAUDE.md` §11) -/

/-- **The hypothesis bundle of `Arlib.gaussianRestricted_isoperimetry_measurable_logTwo` is
satisfiable at data that the open/closed capstone cannot reach.**

`f ≡ 1`, so `h` is the standard Gaussian; `σ = 1`, `d = log 2 / 4`, and the **closed slab**
partition of `Arlib.isPartition3_closedSlab` at `c = 1/4`:

    S₁ = {⟪e,x⟫ ≤ −1/4},   S₂ = {1/4 ≤ ⟪e,x⟫},   S₃ = {−1/4 < ⟪e,x⟫ < 1/4}.

The separation holds on the metric branch: `⟪e, v − u⟫ ≥ 1/2` and `‖e‖ = 1`, so
`‖u − v‖ ≥ 1/2 ≥ 1/4 = d/log 2`.

The last two conjuncts are the point: `S₁` and `S₂` are **not open**
(`Arlib.not_isOpen_inner_le`, `Arlib.not_isOpen_le_inner`), so this data is *outside* the
reach of `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` — the theorem proved here
is being applied where its predecessor cannot be.

`Arlib.exists_enlargements_witness` (`Arlib/Convexity/IsoEnlargeSlack.lean:301`) certifies,
for this same slab data, that the left-hand side `d/σ·(∫_{S₁}h)(∫_{S₂}h)` is **strictly
positive**, so the conclusion here is not the trivial `0 ≤ ·`. -/
theorem gaussianRestricted_isoperimetry_measurable_logTwo_witness (hn : 2 ≤ n) :
    ∃ (f h : EuclideanSpace ℝ (Fin n) → ℝ)
      (S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d B : ℝ),
      0 < σ ∧ 0 < d ∧ (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧
      (∀ x, h x = f x * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) ∧
      Continuous h ∧ (∀ x, h x ≤ B) ∧ Integrable h ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (0 < ∫ x, h x) ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) ∧
      ¬ IsOpen S₁ ∧ ¬ IsOpen S₂ ∧
      d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  classical
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => Real.exp (-‖x‖ ^ 2 / (2 * (1 : ℝ) ^ 2)) with hhdef
  have h0 : ∀ x, 0 ≤ h x := fun x => (Real.exp_pos _).le
  have hhc : Continuous h := by rw [hhdef]; fun_prop
  have hhB : ∀ x, h x ≤ 1 := by
    intro x
    rw [hhdef]
    refine Real.exp_le_one_iff.mpr ?_
    have hx : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) < 2 * (1 : ℝ) ^ 2 := by norm_num
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
  have hhi : Integrable h := by
    have heq : h = fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-(‖x‖ ^ 2) / (2 * 1)) := by
      funext x; rw [hhdef]; norm_num
    rw [heq]
    exact Arlib.GaussianCooling.integrable_gaussian_eucl one_pos
  -- positive total mass, from a floor on the unit ball
  have hlow : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, Real.exp (-(1 : ℝ) / 2) ≤ h x := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [hhdef]
    refine Real.exp_le_exp.mpr ?_
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 2 * (1:ℝ) ^ 2)]
    nlinarith
  have hM : 0 < ∫ x, h x := by
    have hpos := setIntegral_pos_of_ball_le (z := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)
      (c := Real.exp (-(1 : ℝ) / 2)) hhi h0 (by norm_num) (Real.exp_pos _)
      (Set.subset_univ _) hlow
    rwa [setIntegral_univ] at hpos
  -- the slabs
  set S₁ : Set (EuclideanSpace ℝ (Fin n)) := {x | (inner ℝ e x : ℝ) ≤ -(1 / 4 : ℝ)} with hS₁def
  set S₂ : Set (EuclideanSpace ℝ (Fin n)) := {x | (1 / 4 : ℝ) ≤ (inner ℝ e x : ℝ)} with hS₂def
  have hipc : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) := by fun_prop
  have hS₁m : MeasurableSet S₁ := measurableSet_le hipc.measurable measurable_const
  have hS₂m : MeasurableSet S₂ := measurableSet_le measurable_const hipc.measurable
  have hdlog : Real.log 2 / 4 / Real.log 2 = 1 / 4 := by
    have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  refine ⟨fun _ => 1, h, S₁, S₂, {x | -(1/4 : ℝ) < (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) < 1/4},
    1, Real.log 2 / 4, 1, one_pos, by positivity, fun _ => zero_le_one,
    isLogConcave_const zero_le_one, (fun x => by rw [hhdef]; ring), hhc, hhB, hhi,
    isPartition3_closedSlab e (by norm_num), hS₁m, hS₂m,
    (measurableSet_lt measurable_const hipc.measurable).inter
      (measurableSet_lt hipc.measurable measurable_const),
    hM, ?_, not_isOpen_inner_le he _, not_isOpen_le_inner he _, ?_⟩
  · -- the metric branch, at `d/log 2 = 1/4 ≤ 1/2 ≤ ‖u − v‖`
    intro u hu v hv
    left
    rw [hdlog]
    have h1 : (inner ℝ e u : ℝ) ≤ -(1 / 4 : ℝ) := hu
    have h2 : (1 / 4 : ℝ) ≤ (inner ℝ e v : ℝ) := hv
    have hip := abs_real_inner_le_norm e (v - u)
    rw [he, one_mul, inner_sub_right] at hip
    have hle : (inner ℝ e v : ℝ) - (inner ℝ e u : ℝ) ≤ ‖v - u‖ :=
      le_trans (le_abs_self _) hip
    rw [norm_sub_rev] at hle
    linarith
  · -- the conclusion, from the capstone itself
    refine gaussianRestricted_isoperimetry_measurable_logTwo hn one_pos (by positivity)
      (fun _ => zero_le_one) (isLogConcave_const zero_le_one) (fun x => by rw [hhdef]; ring)
      hhc hhB hhi (isPartition3_closedSlab e (by norm_num)) hS₁m hS₂m
      ((measurableSet_lt measurable_const hipc.measurable).inter
        (measurableSet_lt hipc.measurable measurable_const)) hM ?_
    intro u hu v hv
    left
    rw [hdlog]
    have h1 : (inner ℝ e u : ℝ) ≤ -(1 / 4 : ℝ) := hu
    have h2 : (1 / 4 : ℝ) ≤ (inner ℝ e v : ℝ) := hv
    have hip := abs_real_inner_le_norm e (v - u)
    rw [he, one_mul, inner_sub_right] at hip
    have hle : (inner ℝ e v : ℝ) - (inner ℝ e u : ℝ) ≤ ‖v - u‖ :=
      le_trans (le_abs_self _) hip
    rw [norm_sub_rev] at hle
    linarith

section AxiomCheck

#print axioms Arlib.gaussianRestricted_isoperimetry_measurable_logTwo
#print axioms Arlib.ellGaussian_isoperimetry_measurable_logTwo_uncond
#print axioms Arlib.gaussianRestricted_isoperimetry_measurable_logTwo_witness

end AxiomCheck

end Arlib
