/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.Analysis.Convex.Measure
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.LocalizationTransverse

/-!
# Closing up the localisation chain, and positioning its limit segment

`Arlib.exists_flat_cut_chain_collinear` (`Arlib.Convexity.LocalizationAssembly`) produces a
decreasing chain of convex bodies with `∫ g₁ = 0` and `∫ g₂ > 0` throughout and a **collinear**
intersection, but the bodies are built by cutting with `Arlib.halfSpace`, one of whose two sides
is *open*.  `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact`
(`Arlib.Convexity.LocalizationTransverse`) consumes **compact** bodies.  This file bridges that
mismatch, and positions the limit segment along an axis.

## The route taken: closures, not a change of cut

`Arlib.halfSpace` is left exactly as it is — its two sides partition the space, and every
volume-, integral- and partition-level invariant of the chain depends on that.  Instead each body
of the finished chain is replaced by its **closure**.  This is the least invasive change that
delivers compactness, and it costs nothing:

* the chain's *volume-level* invariants (`∫ g₁ = 0`, `0 < ∫ g₂`, `0 < vol`) are unchanged, because
  a convex set differs from its closure inside its frontier, which is Haar-null
  (`Convex.addHaar_frontier`) — `Arlib.setIntegral_closure_of_convex`,
  `Arlib.addHaar_closure_of_convex`;
* the chain's *set-level* invariants survive verbatim, because `closure` is monotone: nestedness
  `D (m+1) ⊆ D m` and containment `D m ⊆ K` are preserved (the latter needs `K` closed, which is
  why `K` is asked to be compact);
* the *cut* invariant is preserved with a **half-turn of the pencil**: the closure of the open side
  `{c < L}` is contained in `{c ≤ L}`, which is `Arlib.halfSpace (-L) (-c) true`
  (`Arlib.closure_halfSpace_false_subset`), and for the pencil `-pencilFun e₁ e₂ θ` is
  `pencilFun e₁ e₂ (θ + π)` with the level flipping in step (`Arlib.pencilFun_add_pi`,
  `Arlib.pencilLevel_add_pi`).  So the closed chain is still cut by *the same family* of pencil
  half-spaces through the same flats, and `Arlib.minor_eq_of_pencil_exhaustion` applies to it
  verbatim — the collinearity of the limit body is inherited, not reproved.

Nothing that consumes `Arlib.halfSpace` changes, so nothing downstream of
`Arlib.exists_flat_cut_chain` is touched.

## Main results

* `Arlib.closure_subset_pencil_halfSpace_true` — the closure of a body cut by a pencil half-space
  lies in a *closed* pencil half-space through the same flat.
* `Arlib.setIntegral_closure_of_convex`, `Arlib.addHaar_closure_of_convex` — closing up a convex
  set changes no Haar volume and no integral.
* `Arlib.exists_flat_cut_chain_collinear_compact` — **the closed chain**: for a compact convex `K`
  a decreasing chain of *compact* convex bodies of positive volume, with `∫ g₁ = 0` and
  `0 < ∫ g₂` at every stage and a collinear intersection.
* `Arlib.exists_flat_cut_chain_collinear_compact_ge` — the same with the quantitative
  `ε · vol (D m) ≤ ∫_{D m} g₂` that the limit passage consumes, obtained by running the chain on
  the perturbed integrand of `Arlib.lt_setIntegral_of_perturbed`.
* `Arlib.exists_mem_iInter_height` — **every height of the slab is attained by the intersection**:
  Cantor's intersection theorem applied to the compact slices `D k ∩ {φ (· - a) = t}`.
* `Arlib.exists_axis_of_collinear` — hence a collinear intersection is *positioned*: there are `b`
  on it and `v` with `φ v = 1` such that every point `y` of it satisfies `y = b + φ (y - b) • v`.
* `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear` — consequently the needle conclusions
  hold with the `haxis` hypothesis of `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact`
  replaced by the purely geometric `Collinear ℝ (⋂ k, D k)`, which is exactly what the localisation
  chain delivers; the axis is produced, not assumed.

## What is still missing — read `Arlib.exists_mem_iInter_height` first

`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` carries **both** `hslab` (every body lies
in the slab `{y | φ (y - a) ∈ [0,1]}`) and `hspan` (every body meets every height of that slab).
Together these force `φ '' (D k - a) = Icc 0 1` for **every** `k`: the bodies of the chain all have
*the same* extent in the height direction, and by `Arlib.exists_mem_iInter_height` so does their
intersection.  In other words the limiting needle must be a chord realising the full height of
`D 0` itself.

The flat-cut chain gives no such control: its bodies shrink in every direction, so for a generic
chain there is **no** nonzero `φ` whose range is constant along it (take `D k` a `1/k`-neighbourhood
of the limit segment: `φ '' D k` shrinks strictly for every `φ ≠ 0`).  Normalising the *limit
segment* to unit height gives `hspan` for free and breaks `hslab`; normalising `D 0` gives `hslab`
for free and breaks `hspan`.  So the remaining obstruction between
`Arlib.exists_flat_cut_chain_collinear_compact` and the Localization Lemma in general position is
**not** closedness, and not the positioning either — both are discharged here — but the rigidity of
the `hslab`/`hspan` pair, which asks the needle to span the starting body.  Relaxing it means
letting the slab of the `k`-th body shrink to the slab of the needle, i.e. a change to the limit
passage of `Arlib.Convexity.NeedleLimit`, not to the chain.
-/

open MeasureTheory Set Filter Topology

namespace Arlib

/-! ### Closing up a pencil cut -/

section PencilClosure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The closure of a pencil cut is again a pencil cut, on the closed side.**

If `D` lies on *either* side of a hyperplane of the pencil through the flat
`{⟪d₁,·⟫ = r} ∩ {⟪d₂,·⟫ = s}`, then `closure D` lies in the **closed** side `{L ≤ c}` of a
hyperplane of the *same* pencil through the *same* flat: for the already closed side nothing
happens, and for the open side one takes the half-turn `θ + π`, which negates both the functional
and the level (`Arlib.pencilFun_add_pi`, `Arlib.pencilLevel_add_pi`) and so turns `{c < L}` into
`{-L ≤ -c}`. -/
theorem closure_subset_pencil_halfSpace_true {d₁ d₂ : E} {D : Set E} {θ r s : ℝ} {side : Bool}
    (hD : D ⊆ halfSpace (pencilFun d₁ d₂ θ) (pencilLevel r s θ) side) :
    ∃ θ' : ℝ, closure D ⊆ halfSpace (pencilFun d₁ d₂ θ') (pencilLevel r s θ') true := by
  cases side
  · refine ⟨θ + Real.pi, ?_⟩
    rw [pencilFun_add_pi, pencilLevel_add_pi]
    exact (closure_mono hD).trans (closure_halfSpace_false_subset _ _)
  · exact ⟨θ, by simpa only [closure_halfSpace_true] using closure_mono hD⟩

end PencilClosure

/-! ### Closing up a convex body changes no volume and no integral -/

section ConvexClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A convex set agrees with its closure up to a Haar-null set: the difference lies in the
frontier, which is null by `Convex.addHaar_frontier`. -/
theorem ae_eq_closure_of_convex {C : Set E} (hC : Convex ℝ C) : (closure C : Set E) =ᵐ[μ] C := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null (fun x hx => ?_) (Convex.addHaar_frontier μ hC)
    exact ⟨hx.1, fun hmem => hx.2 (interior_subset hmem)⟩
  · simp [Set.sdiff_eq_empty.mpr subset_closure]

/-- **Closing up a convex set does not change its Haar volume.** -/
theorem addHaar_closure_of_convex {C : Set E} (hC : Convex ℝ C) : μ (closure C) = μ C :=
  measure_congr (ae_eq_closure_of_convex μ hC)

/-- **Closing up a convex set does not change any integral over it.**  This is why the mass
invariants of the localisation chain — which are all volume-level — survive the passage to
closures unchanged. -/
theorem setIntegral_closure_of_convex {C : Set E} (hC : Convex ℝ C) (f : E → ℝ) :
    ∫ x in closure C, f x ∂μ = ∫ x in C, f x ∂μ :=
  setIntegral_congr_set (ae_eq_closure_of_convex μ hC)

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- A set carrying positive mass has positive measure. -/
theorem measure_pos_of_setIntegral_pos {C : Set E} {f : E → ℝ} (h : 0 < ∫ x in C, f x ∂μ) :
    0 < μ C := by
  rcases eq_or_ne (μ C) 0 with hzero | hne
  · rw [Measure.restrict_eq_zero.mpr hzero, integral_zero_measure] at h
    exact absurd h (lt_irrefl 0)
  · exact pos_iff_ne_zero.mpr hne

end ConvexClosure

/-! ### The closed localisation chain -/

section CompactChain

variable {n : ℕ}

/-- **The localisation chain with compact bodies.**

The chain of `Arlib.exists_flat_cut_chain_collinear`, closed up.  For a **compact** convex `K`
with `∫_K g₁ = 0` and `0 < ∫_K g₂` there is a decreasing chain `K = D 0 ⊇ D 1 ⊇ ⋯` of *compact*
convex bodies of **positive volume**, with `∫_{D m} g₁ = 0` exactly and `0 < ∫_{D m} g₂` at every
stage, whose intersection is collinear.

Compactness is what `Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` asks of the bodies,
and it is obtained here without touching `Arlib.halfSpace`: closure is monotone, so nestedness and
containment in `K` are preserved; the frontier of a convex set is Haar-null, so no volume and no
integral moves; and a half-turn of the pencil turns the closure of the open side of a cut into the
closed side of another cut through the same flat, so the combinatorial thinness argument
(`Arlib.minor_eq_of_pencil_exhaustion`) applies to the closed chain unchanged. -/
theorem exists_flat_cut_chain_collinear_compact (hn : 2 ≤ n)
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ} (hg₁ : Integrable g₁) (hg₂ : Integrable g₂)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hz : ∫ x in K, g₁ x = 0) (hp : 0 < ∫ x in K, g₂ x) :
    ∃ D : ℕ → Set (EuclideanSpace ℝ (Fin n)), D 0 = K ∧ (∀ m, D (m + 1) ⊆ D m) ∧
      (∀ m, IsCompact (D m) ∧ Convex ℝ (D m) ∧ D m ⊆ K ∧ 0 < volume (D m) ∧
        (∫ x in D m, g₁ x) = 0 ∧ 0 < ∫ x in D m, g₂ x) ∧
      Collinear ℝ (⋂ m, D m) := by
  classical
  have hKcl : closure K = K := hK.isClosed.closure_eq
  have hne : Nonempty {p : Fin n × Fin n // p.1 ≠ p.2} :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ({p : Fin n × Fin n // p.1 ≠ p.2} × ℚ × ℚ), Function.Surjective f :=
    exists_surjective_nat _
  obtain ⟨C, hC0, hCmono, hCinv, hCcut⟩ := exists_flat_cut_chain
    (d₁ := fun m => EuclideanSpace.single (f m).1.1.1 (1 : ℝ))
    (d₂ := fun m => EuclideanSpace.single (f m).1.1.2 (1 : ℝ))
    (fun m => inner_single_one_self _) (fun m => inner_single_one_self _)
    (fun m => inner_single_one_ne (f m).1.2)
    (fun m => ((f m).2.1 : ℝ)) (fun m => ((f m).2.2 : ℝ)) hK.measurableSet hg₁ hg₂ hz hp
  have hconv : ∀ m, Convex ℝ (C m) := fun m => (hCinv m).2.2.1 hKconv
  have hsub : ∀ m, closure (C m) ⊆ K := fun m => by
    rw [← hKcl]; exact closure_mono (hCinv m).2.1
  refine ⟨fun m => closure (C m), by show closure (C 0) = K; rw [hC0]; exact hKcl,
    fun m => closure_mono (hCmono m),
    fun m => ⟨hK.of_isClosed_subset isClosed_closure (hsub m), (hconv m).closure, hsub m, ?_, ?_,
      ?_⟩, ?_⟩
  · rw [addHaar_closure_of_convex volume (hconv m)]
    exact measure_pos_of_setIntegral_pos volume (hCinv m).2.2.2.2
  · rw [setIntegral_closure_of_convex volume (hconv m)]; exact (hCinv m).2.2.2.1
  · rw [setIntegral_closure_of_convex volume (hconv m)]; exact (hCinv m).2.2.2.2
  · refine collinear_of_minor_eq (fun x hx y hy z hz' => ?_)
    refine minor_eq_of_pencil_exhaustion
      (convex_iInter fun m => (hconv m).closure) (fun i j hij r s => ?_) hx hy hz'
    obtain ⟨m, hm⟩ := hf (⟨(i, j), hij⟩, r, s)
    obtain ⟨θ, side, hcut⟩ := hCcut m
    rw [hm] at hcut
    obtain ⟨θ', hθ'⟩ := closure_subset_pencil_halfSpace_true hcut
    exact ⟨θ', true, (iInter_subset _ (m + 1)).trans hθ'⟩

/-- **The closed localisation chain, with the quantitative lower bound.**

`Arlib.exists_flat_cut_chain_collinear_compact` run on the perturbed integrand
`g₂ - ε · 1_K` of `Arlib.lt_setIntegral_of_perturbed`: the invariant `0 < ∫_{D m} g₂` is upgraded
to `ε · vol (D m) ≤ ∫_{D m} g₂`, which is the form the limit passage
(`Arlib.needleIntegral_eq_zero_and_ge`) consumes.  Only `g₂` needs a perturbation; the equality
`∫_{D m} g₁ = 0` is maintained for free by the bisection. -/
theorem exists_flat_cut_chain_collinear_compact_ge (hn : 2 ≤ n)
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℝ} (hg₁ : Integrable g₁) (hg₂ : Integrable g₂)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hz : ∫ x in K, g₁ x = 0) {ε : ℝ} (hp : ε * (volume K).toReal < ∫ x in K, g₂ x) :
    ∃ D : ℕ → Set (EuclideanSpace ℝ (Fin n)), D 0 = K ∧ (∀ m, D (m + 1) ⊆ D m) ∧
      (∀ m, IsCompact (D m) ∧ Convex ℝ (D m) ∧ D m ⊆ K ∧ 0 < volume (D m) ∧
        (∫ x in D m, g₁ x) = 0 ∧ ε * (volume (D m)).toReal ≤ ∫ x in D m, g₂ x) ∧
      Collinear ℝ (⋂ m, D m) := by
  have hKm : MeasurableSet K := hK.measurableSet
  have hKfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hind : Integrable (K.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hKm).mpr (integrableOn_const hKfin)
  have hg₂' : Integrable fun x => g₂ x - ε * K.indicator (fun _ => (1 : ℝ)) x :=
    hg₂.sub (hind.const_mul ε)
  have hp' : 0 < ∫ x in K, (g₂ x - ε * K.indicator (fun _ => (1 : ℝ)) x) := by
    have hcongr : (∫ x in K, (g₂ x - ε * K.indicator (fun _ => (1 : ℝ)) x))
        = ∫ x in K, (g₂ x - ε) :=
      setIntegral_congr_fun hKm fun x hx => by
        rw [Set.indicator_of_mem hx, mul_one]
    rw [hcongr, integral_sub hg₂.integrableOn (integrableOn_const hKfin), setIntegral_const,
      smul_eq_mul, Measure.real]
    linarith
  obtain ⟨D, hD0, hDmono, hDinv, hDcol⟩ :=
    exists_flat_cut_chain_collinear_compact hn hg₁ hg₂' hK hKconv hz hp'
  refine ⟨D, hD0, hDmono, fun m => ⟨(hDinv m).1, (hDinv m).2.1, (hDinv m).2.2.1,
    (hDinv m).2.2.2.1, (hDinv m).2.2.2.2.1, ?_⟩, hDcol⟩
  exact (lt_setIntegral_of_perturbed (hDinv m).2.2.1 (hDinv m).1.measurableSet
    (hDinv m).1.measure_lt_top.ne hg₂.integrableOn (hDinv m).2.2.2.2.2).le

/-- **Non-vacuity of the closed localisation chain.**

Every hypothesis of `Arlib.exists_flat_cut_chain_collinear_compact` is met simultaneously by the
closed unit ball of the Euclidean plane with `g₁ = 0` and `g₂` the indicator of that ball, and the
chain it produces consists of *compact* convex bodies of *positive* volume with positive
`g₂`-mass at every stage and a collinear intersection.  So the closed chain is not a statement
about an empty configuration.

As in `Arlib.exists_flat_cut_chain_collinear_ball`, `g₁ = 0` is the degenerate-but-legitimate
choice: what the witness certifies is that the typeclass bundle, the compactness and
integrability hypotheses, and the two mass invariants can hold at once with `0 < ∫ g₂`. -/
theorem exists_flat_cut_chain_collinear_compact_ball :
    ∃ D : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
      D 0 = Metric.closedBall 0 1 ∧ (∀ m, D (m + 1) ⊆ D m) ∧
      (∀ m, IsCompact (D m) ∧ Convex ℝ (D m) ∧ D m ⊆ Metric.closedBall 0 1 ∧
        0 < volume (D m) ∧ (∫ _x in D m, (0 : ℝ)) = 0 ∧
        0 < ∫ x in D m, Set.indicator (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
          (fun _ => (1 : ℝ)) x) ∧
      Collinear ℝ (⋂ m, D m) := by
  have hKc : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isCompact_closedBall _ _
  have hKm : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    measurableSet_closedBall
  have hKfin : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hKpos : 0 < volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.measure_closedBall_pos volume 0 one_pos
  have hg₂ : Integrable (Set.indicator (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (fun _ => (1 : ℝ))) := (integrable_indicator_iff hKm).mpr (integrableOn_const hKfin)
  have hp : 0 < ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      Set.indicator (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (fun _ => (1 : ℝ)) x := by
    rw [setIntegral_indicator hKm, Set.inter_self, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def]
    exact ENNReal.toReal_pos hKpos.ne' hKfin
  exact exists_flat_cut_chain_collinear_compact (by norm_num) (integrable_zero _ _ _) hg₂ hKc
    (convex_closedBall _ _) (integral_zero _ _) hp

end CompactChain

/-! ### Positioning a collinear limit body along an axis -/

section Axis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Every height of the slab is attained by the intersection of the chain.**

If the bodies `D k` are compact and decreasing and each of them meets every height `t ∈ [0,1]` of
the slab measured by `φ (· - a)`, then so does `⋂ k, D k`.  This is Cantor's intersection theorem
applied to the compact slices `D k ∩ {y | φ (y - a) = t}`.

Read together with the hypothesis `hslab` of
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` this says that a chain satisfying both
`hslab` and `hspan` has **the same height range `[0,1]` at every stage, including in the limit** —
the needle it produces must realise the full height of `D 0`. -/
theorem exists_mem_iInter_height {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDmono : ∀ k, D (k + 1) ⊆ D k) {a : E} {φ : E →ₗ[ℝ] ℝ}
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ∃ y ∈ ⋂ k, D k, φ (y - a) = t := by
  have hHclosed : IsClosed {y : E | φ (y - a) = t} :=
    isClosed_eq ((φ.continuous_of_finiteDimensional).comp (continuous_id.sub continuous_const))
      continuous_const
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k => D k ∩ {y : E | φ (y - a) = t})
    (fun k => Set.inter_subset_inter_left _ (hDmono k))
    (fun k => by obtain ⟨y, hy, hyt⟩ := hspan k t ht; exact ⟨y, hy, hyt⟩)
    ((hDcomp 0).inter_right hHclosed) (fun k => (hDcomp k).isClosed.inter hHclosed)
  exact ⟨y, Set.mem_iInter.mpr fun k => (Set.mem_iInter.mp hy k).1, (Set.mem_iInter.mp hy 0).2⟩

/-- **A collinear limit body is positioned by the slab it spans.**

If the compact decreasing bodies `D k` all meet every height of the slab measured by
`φ (· - a)` and their intersection is *collinear*, then that intersection is a subset of an
explicitly positioned axis: there are a base point `b` at height `0` and a direction `v` with
`φ v = 1` such that every `y` of the intersection satisfies `y = b + φ (y - b) • v`.

Moreover `φ b = φ a`, so heights measured from `b` are the same as heights measured from `a` and
the `hslab`/`hspan` hypotheses transfer to the new base point unchanged.  This is the elementary
"rescale the segment to unit height" step: the endpoints are the points of the intersection at
heights `0` and `1` (`Arlib.exists_mem_iInter_height`), and `v` is their difference. -/
theorem exists_axis_of_collinear {D : ℕ → Set E} (hDcomp : ∀ k, IsCompact (D k))
    (hDmono : ∀ k, D (k + 1) ⊆ D k) {a : E} {φ : E →ₗ[ℝ] ℝ}
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
    (hcol : Collinear ℝ (⋂ k, D k)) :
    ∃ b v : E, φ b = φ a ∧ φ v = 1 ∧ ∀ y ∈ ⋂ k, D k, y = b + φ (y - b) • v := by
  obtain ⟨y₀, hy₀, h0⟩ :=
    exists_mem_iInter_height hDcomp hDmono hspan (left_mem_Icc.mpr zero_le_one)
  obtain ⟨y₁, hy₁, h1⟩ :=
    exists_mem_iInter_height hDcomp hDmono hspan (right_mem_Icc.mpr zero_le_one)
  rw [map_sub] at h0 h1
  obtain ⟨w, hw⟩ := (collinear_iff_of_mem hy₀).mp hcol
  obtain ⟨r₁, hr₁⟩ := hw y₁ hy₁
  have hy₁w : y₁ = r₁ • w + y₀ := by simpa only [vadd_eq_add] using hr₁
  have hkey : r₁ * φ w = 1 := by
    have h : φ y₁ = r₁ * φ w + φ y₀ := by rw [hy₁w, map_add, map_smul, smul_eq_mul]
    linarith
  refine ⟨y₀, r₁ • w, by linarith, by rw [map_smul, smul_eq_mul, hkey], fun y hy => ?_⟩
  obtain ⟨r, hr⟩ := hw y hy
  have hyw : y = r • w + y₀ := by simpa only [vadd_eq_add] using hr
  have hheight : φ (y - y₀) = r * φ w := by
    rw [hyw, add_sub_cancel_right, map_smul, smul_eq_mul]
  rw [hheight, smul_smul, hyw]
  have hcoef : r * φ w * r₁ = r := by
    have : r * (r₁ * φ w) = r := by rw [hkey, mul_one]
    linarith [this, mul_comm (φ w) r₁]
  rw [hcoef, add_comm]

end Axis

/-! ### The needle conclusions from a *collinear* limit body -/

section Collinear

variable {m : ℕ}

/-- **The localisation needle from a compact chain with a collinear limit body.**

`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact` with its `haxis` hypothesis — "every
point of `⋂ k, D k` lies on the prescribed needle axis" — replaced by the purely geometric
`Collinear ℝ (⋂ k, D k)`, which is exactly what `Arlib.exists_flat_cut_chain_collinear_compact`
delivers.  The axis is **produced**, not assumed: `Arlib.exists_axis_of_collinear` reads the base
point and the direction off the two points of the intersection at heights `0` and `1`, whose
existence is Cantor's intersection theorem (`Arlib.exists_mem_iInter_height`).

The bodies are still asked to lie in (`hslab`) and span (`hspan`) the slab
`{y | φ (y - a) ∈ [0,1]}`; see the module docstring for why that pair, and not closedness or
positioning, is what still separates this from the Localization Lemma in general position.

As at the origin `Arlib.exists_needleIntegral_eq_zero_and_pos`, the profile is delivered
**supported in `[0,1]` and integrable**; the transport reuses the same `W`, so both properties
pass through verbatim. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_collinear (hm : m ≠ 0)
    {a : Fin (m + 1) → ℝ} {φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ}
    {D : ℕ → Set (Fin (m + 1) → ℝ)} (hDconv : ∀ k, Convex ℝ (D k))
    (hDcomp : ∀ k, IsCompact (D k)) (hDmono : ∀ k, D (k + 1) ⊆ D k)
    (hDpos : ∀ k, 0 < volume (D k))
    (hslab : ∀ k, ∀ y ∈ D k, φ (y - a) ∈ Icc (0 : ℝ) 1)
    (hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - a) = t)
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
  obtain ⟨b, v, hb, hφv, haxis⟩ := exists_axis_of_collinear hDcomp hDmono hspan hcol
  have hshift : ∀ y : Fin (m + 1) → ℝ, φ (y - b) = φ (y - a) := by
    intro y; rw [map_sub, map_sub, hb]
  obtain ⟨W, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_compact hm hφv
    hDconv hDcomp hDmono hDpos (fun k y hy => by rw [hshift]; exact hslab k y hy)
    (fun k t ht => by
      obtain ⟨y, hy, hyt⟩ := hspan k t ht
      exact ⟨y, hy, by rw [hshift]; exact hyt⟩)
    haxis hg₁ hg₂ hM₁ hM₂ hzero hεpos hge
  exact ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, hW₁, hW₂⟩

/-- **Non-vacuity of `Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear`.**

The shrinking boxes `D k = [0,1] × [0, 1/(k+1)]^m` of
`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_box` satisfy every hypothesis of the
collinear form as well: they are convex, compact, decreasing, of *positive* volume, they sit in
and span the slab `{y | y 0 ∈ [0,1]}`, and their intersection is the segment `[0, e₀]`, which is
**collinear**.  The profile that comes out is nonzero, since its integral is positive.

This is the check that the collinear form is not a statement about an empty configuration: the
`haxis` hypothesis of the compact form has genuinely been *replaced* by `Collinear`, not merely
renamed. -/
theorem exists_needleIntegral_eq_zero_and_pos_of_collinear_box (hm : m ≠ 0) :
    ∃ (b v : Fin (m + 1) → ℝ) (W : ℝ → ℝ),
      (LinearMap.proj (0 : Fin (m + 1)) : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ) v = 1 ∧ (∀ t, 0 ≤ W t) ∧
      (∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 → W t = 0) ∧ Integrable W ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun t => W t ^ (1 / (m : ℝ))) ∧
      0 < ∫ t : ℝ, W t * (1 : ℝ) := by
  classical
  set r : ℕ → Fin (m + 1) → ℝ := fun k i => if i = 0 then 1 else 1 / ((k : ℝ) + 1) with hr
  have hrpos : ∀ k i, 0 < r k i := by
    intro k i
    rw [hr]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      positivity
  set D : ℕ → Set (Fin (m + 1) → ℝ) := fun k => univ.pi fun i => Icc (0 : ℝ) (r k i) with hD
  have hDcomp : ∀ k, IsCompact (D k) := fun k => isCompact_univ_pi fun _ => isCompact_Icc
  have hDconv : ∀ k, Convex ℝ (D k) := fun k => convex_pi fun _ _ => convex_Icc _ _
  have hDmono : ∀ k, D (k + 1) ⊆ D k := by
    intro k y hy
    refine Set.mem_univ_pi.mpr fun i => ?_
    have hyi := Set.mem_univ_pi.mp hy i
    refine Set.Icc_subset_Icc_right ?_ hyi
    rw [hr]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
      exact one_div_le_one_div_of_le h1 h2
  have hvol : ∀ k, volume (D k) = ∏ i : Fin (m + 1), ENNReal.ofReal (r k i) := by
    intro k
    rw [hD]
    simp only [volume_pi_pi, Real.volume_Icc, sub_zero]
  have hDpos : ∀ k, 0 < volume (D k) := by
    intro k
    rw [hvol k, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => (ENNReal.ofReal_pos.mpr (hrpos k i)).ne'
  set φ : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0 with hφ
  have hslab : ∀ k, ∀ y ∈ D k, φ (y - 0) ∈ Icc (0 : ℝ) 1 := by
    intro k y hy
    have h0 := Set.mem_univ_pi.mp hy 0
    rw [hr] at h0
    simpa [hφ] using h0
  have hspan : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, ∃ y ∈ D k, φ (y - 0) = t := by
    intro k t ht
    refine ⟨fun i => if i = 0 then t else 0, Set.mem_univ_pi.mpr fun i => ?_, by simp [hφ]⟩
    by_cases hi : i = 0
    · simp only [hi, if_true, hr]
      simpa using ht
    · simp only [hi, if_false]
      exact ⟨le_rfl, (hrpos k i).le⟩
  have hcol : Collinear ℝ (⋂ k, D k) := by
    refine (collinear_iff_of_mem (p₀ := (0 : Fin (m + 1) → ℝ)) ?_).mpr
      ⟨Pi.single 0 1, fun y hy => ⟨y 0, ?_⟩⟩
    · refine Set.mem_iInter.mpr fun k => Set.mem_univ_pi.mpr fun i => ?_
      exact ⟨le_rfl, (hrpos k i).le⟩
    · have hy' : ∀ k, y ∈ D k := fun k => Set.mem_iInter.mp hy k
      have hzero : ∀ i : Fin (m + 1), i ≠ 0 → y i = 0 := by
        intro i hi
        refine le_antisymm ?_ ((Set.mem_univ_pi.mp (hy' 0) i).1)
        by_contra hcon
        rw [not_le] at hcon
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hcon
        have := (Set.mem_univ_pi.mp (hy' n) i).2
        rw [hr] at this
        simp only [hi, if_false] at this
        linarith
      funext i
      by_cases hi : i = 0
      · simp [hi]
      · simp [hi, hzero i hi]
  obtain ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, -, hW₂⟩ :=
    exists_needleIntegral_eq_zero_and_pos_of_collinear hm hDconv hDcomp hDmono hDpos hslab hspan
      hcol (g₁ := fun _ => (0 : ℝ)) (g₂ := fun _ => (1 : ℝ)) continuous_const continuous_const
      (M := 1) (fun _ => by norm_num) (fun _ => by norm_num) (fun k => integral_zero _ _)
      (ε := 1) one_pos
      (fun k => by rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, one_mul])
  exact ⟨b, v, W, hφv, hW0, hWsupp, hWint, hWc, hW₂⟩

end Collinear

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.closure_subset_pencil_halfSpace_true
#print axioms Arlib.ae_eq_closure_of_convex
#print axioms Arlib.addHaar_closure_of_convex
#print axioms Arlib.setIntegral_closure_of_convex
#print axioms Arlib.measure_pos_of_setIntegral_pos
#print axioms Arlib.exists_flat_cut_chain_collinear_compact
#print axioms Arlib.exists_flat_cut_chain_collinear_compact_ge
#print axioms Arlib.exists_flat_cut_chain_collinear_compact_ball
#print axioms Arlib.exists_mem_iInter_height
#print axioms Arlib.exists_axis_of_collinear
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear
#print axioms Arlib.exists_needleIntegral_eq_zero_and_pos_of_collinear_box
