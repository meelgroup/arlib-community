/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.Warmness
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Pointwise closeness, and why mixing does not deliver it

`AUDIT-KV97.md` §4b records the sharpest discrepancy found in the Kannan–Vempala
formalisation.  Both KV97's Theorem 2 and the consuming paper state the hypothesis on the
continuous draw as *"`p` is drawn from a density whose **variational distance** to uniform
on `P'` is at most `ε`"*, and both then use the conclusion as if `ε` were a **relative**
error.  It is not: a total-variation hypothesis buys only an *additive* error, because the
integrand lies in `[0,1]` and `|∫f dμ − ∫f dν| ≤ TV(μ,ν)` is sharp
(`Arlib.TVLe.integral_le`).  Under the additive reading the corollary is false — summing
over the `N` lattice points contributes `N·ε`, which does not cancel.  So
`Arlib.KV97.theorem2` takes a **pointwise** hypothesis, `(1−ε)/V ≤ f p ≤ (1+ε)/V`.

The consequence for the sampler is what this file is about.  A mixing-time bound
(`Arlib.MarkovChains.MixesWithin`, `Arlib.MarkovChains.mixesWithin_of_conductance_decay`)
delivers **total variation** and nothing else.  Getting from there to a pointwise bound is a
further argument that neither paper gives.  This file settles what that argument must
contain.

## The three findings

1. **Pointwise closeness implies a total-variation bound, with no loss**
   (`PointwiseClose.tvLe`), and **the converse fails as badly as it possibly can**.  For
   every `δ ≠ 0` there are two probability measures on `Bool` at total variation distance at
   most `δ` which are not pointwise `ε`-close for **any** `ε`, `ε = ⊤` included
   (`exists_tvLe_not_pointwiseClose_forall`, `not_exists_pointwiseClose_of_tvLe`); and even
   restricting to pairs with `μ ≪ ν`, no `ε` survives once `δ` is small
   (`exists_tvLe_not_pointwiseClose`).  **No amount of mixing, on its own, gives a pointwise
   bound.**  See the counterexample section for the two measures, spelled out.

2. **Uniform minorisation is a sufficient extra hypothesis, and the whole argument runs on
   it.**  If the kernel satisfies Doeblin's condition `c * pi S ≤ P x S` for every `x`
   (`UniformMinorisation`) and `pi` is stationary, then from an `M`-warm start the law after
   `t` steps is squeezed between `(1 − (1−c)^t) • pi` and `(1 + (1−c)^t (M−1)) • pi`
   (`minorises_iterate_of_uniformMinorisation`, `isWarm_iterate_of_uniformMinorisation`),
   hence is pointwise `ε`-close as soon as `(1−c)^t · max(1, M−1) ≤ ε`
   (`pointwiseClose_iterate_of_uniformMinorisation`, `eventually_pointwiseClose_iterate`).
   Note the rate is `1 − c`: **no conductance, isoperimetry or spectral gap appears.**

3. **The ball walk does not satisfy uniform minorisation** — and the reason is worse than
   the boundary degeneracy one might expect.  See the verdict below.

## Verdict on the ball walk

`Arlib.MarkovChains.ballWalk K δ` (built and proved reversible in `BallWalk.lean`) **does
not** satisfy `UniformMinorisation (ballWalk K δ) (uniformOn volume K) c` for any `c ≠ 0`,
on any `K` of diameter greater than `δ`.  The obstruction is *locality*, not the boundary:

* one step of the walk from `x` is supported in `Metric.ball x δ ∪ {x}` — this is immediate
  from `Arlib.MarkovChains.ballWalk_apply_set`, whose two terms are
  `(vol (ball x δ))⁻¹ * vol (T ∩ ball x δ ∩ K)` and `(1 − ℓ(x)) * 1_T(x)`;
* so if `S ⊆ K` is a positive-volume chunk of `K` with `S ∩ ball x δ = ∅` and `x ∉ S` — which
  exists whenever `K` has diameter greater than `δ` and is not concentrated near `x` — then
  `ballWalk K δ x S = 0` while `uniformOn volume K S > 0`;
* `not_uniformMinorisation_of_unreachable` then rules out every `c ≠ 0`.

This is stated abstractly in this file rather than proved for `ballWalk`, because the
instantiation needs volume computations that belong with `BallWalk.lean`; the two lemmas
`measure_eq_zero_of_uniformMinorisation` and `not_uniformMinorisation_of_unreachable`
are the whole of the argument, and only the "there is a far chunk" geometry is left.

**The degeneracy of the local conductance `Arlib.MarkovChains.ell K δ x` near `∂K` is a
*second*, independent obstruction**, and it is the one Cousins–Vempala actually work
around: `ℓ(x) → 0` as `x → ∂K` makes the walk hold at `x` with probability `→ 1`, which is
why they pass to the **speedy walk** and restrict to `Arlib.MarkovChains.SpeedyPoints K δ
= {x | 3/4 ≤ ℓ(x)}` (`vol3_journal.tex:829`).  Restricting to speedy points fixes the
holding probability; it does **not** fix locality, so it does not produce a minorisation
either.

**So the honest verdict is: uniform minorisation is the wrong hypothesis for this
application.**  A local walk can only be minorised after `t₀` steps, where `t₀` is enough to
cross `K`, and the constant it gets there is tiny: reaching a far chunk of `K` requires the
walk to traverse a corridor of `Θ(D/δ)` balls, and the probability of doing so is
exponentially small in that number of steps.  Feeding such a `c` into
`eventually_pointwiseClose_iterate` gives a bound far worse than the `O*(n³)` the
conductance route gives *for total variation* — so this is not merely a formalisation gap,
it is the wrong theorem for the application.

What this means for the programme: **the TV → pointwise gap is not closed by the mixing
machinery and is not closed here.**  The routes that remain, none of which this file
formalises, are (a) prove the pointwise bound for the *whole trajectory* by a local
Harnack/smoothing estimate on the ball-walk density, which is what "one more step of a
δ-ball average makes the density Hölder" would give; (b) change the reduction so that
KV97's Theorem 2 consumes an additive error, which `AUDIT-KV97.md` §4b argues is impossible
at the required scale `1/Vol(P')`; or (c) supply the pointwise draw by rejection against a
proposal whose density is known exactly, paying an acceptance-probability factor.  Naming
this precisely is the point of the file: the roadmap did not anticipate it.

## Main definitions

* `Arlib.MarkovChains.PointwiseClose μ ν ε` — `μ ≪ ν` and `1 − ε ≤ dμ/dν ≤ 1 + ε` a.e.
* `Arlib.MarkovChains.Minorises m μ ν` — the setwise lower bound `m * ν S ≤ μ S`, the mirror
  image of `Arlib.IsWarm`.
* `Arlib.MarkovChains.UniformMinorisation P pi c` — Doeblin's condition.
* `Arlib.MarkovChains.twoPoint p` — the two-point law on `Bool` carrying the counterexample.

## Main results

* `PointwiseClose.tvLe` — pointwise `ε` implies `TVLe … ε`, with the same constant.
* `pointwiseClose_iff_isWarm_and_minorises` — pointwise closeness *is* the pair of setwise
  bounds `IsWarm (1+ε)` and `Minorises (1−ε)`; this is how such a bound gets built.
* `exists_tvLe_not_pointwiseClose_forall`, `exists_tvLe_not_pointwiseClose`,
  `not_exists_pointwiseClose_of_tvLe` — **the counterexample**.
* `pointwiseClose_iterate_of_uniformMinorisation`, `eventually_pointwiseClose_iterate` — the
  Doeblin route, with an explicit threshold.
* `exists_uniformMinorisation_and_pointwiseClose` — the non-vacuity witness (`CLAUDE.md`
  §11): `Kernel.const Ω pi` is minorised at rate `1` and reaches `PointwiseClose … 0` in one
  step, and is the same chain that witnesses `MixesWithin _ _ _ 1 0`.
* `not_uniformMinorisation_of_unreachable` — the obstruction, abstractly.

## Scope

There is **no** predicate here whose name asserts that mixing gives pointwise closeness,
because there is no such theorem; `PointwiseClose` is about a pair of measures and says
nothing about a chain.  Nothing here imports or mentions `ballWalk`: the verdict above is
analysis, recorded in prose, with the abstract half of it mechanised.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Pointwise closeness -/

/-- **`μ` is pointwise `ε`-close to `ν`**: `μ` has a density with respect to `ν` and that
density lies in `[1 - ε, 1 + ε]` almost everywhere. -/
def PointwiseClose (μ ν : Measure Ω) (ε : ℝ≥0∞) : Prop :=
  μ ≪ ν ∧ ∀ᵐ x ∂ν, 1 - ε ≤ μ.rnDeriv ν x ∧ μ.rnDeriv ν x ≤ 1 + ε

/-- Unfolding lemma for `PointwiseClose`. -/
theorem pointwiseClose_iff (μ ν : Measure Ω) (ε : ℝ≥0∞) :
    PointwiseClose μ ν ε ↔
      μ ≪ ν ∧ ∀ᵐ x ∂ν, 1 - ε ≤ μ.rnDeriv ν x ∧ μ.rnDeriv ν x ≤ 1 + ε := Iff.rfl

/-- Pointwise closeness entails absolute continuity — by definition, but worth a name:
this is the half of the notion that a total-variation bound does not give at all. -/
theorem PointwiseClose.absolutelyContinuous {μ ν : Measure Ω} {ε : ℝ≥0∞}
    (h : PointwiseClose μ ν ε) : μ ≪ ν := h.1

/-- The upper half of the density bound. -/
theorem PointwiseClose.rnDeriv_le {μ ν : Measure Ω} {ε : ℝ≥0∞} (h : PointwiseClose μ ν ε) :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ 1 + ε := h.2.mono fun _ hx => hx.2

/-- The lower half of the density bound. -/
theorem PointwiseClose.le_rnDeriv {μ ν : Measure Ω} {ε : ℝ≥0∞} (h : PointwiseClose μ ν ε) :
    ∀ᵐ x ∂ν, 1 - ε ≤ μ.rnDeriv ν x := h.2.mono fun _ hx => hx.1

/-- **A pointwise bound may always be weakened.** -/
theorem PointwiseClose.mono {μ ν : Measure Ω} {ε ε' : ℝ≥0∞} (h : PointwiseClose μ ν ε)
    (hε : ε ≤ ε') : PointwiseClose μ ν ε' :=
  ⟨h.1, h.2.mono fun _ hx => ⟨(tsub_le_tsub_left hε 1).trans hx.1, hx.2.trans (by gcongr)⟩⟩

/-- **A measure is pointwise `0`-close to itself.** -/
@[simp] theorem pointwiseClose_self (μ : Measure Ω) [SigmaFinite μ] :
    PointwiseClose μ μ 0 := by
  refine ⟨Measure.AbsolutelyContinuous.refl μ, ?_⟩
  filter_upwards [μ.rnDeriv_self] with x hx
  simp [hx]

/-! ## The setwise form of a two-sided density bound

`Arlib.IsWarm M μ ν` is the setwise *upper* bound `μ S ≤ M * ν S`. `Minorises` below is
its mirror image, the setwise *lower* bound. A pointwise `ε`-closeness is exactly the
conjunction `IsWarm (1 + ε)` and `Minorises (1 - ε)`, and the two directions of that
equivalence are `PointwiseClose.isWarm`/`PointwiseClose.minorises` and
`pointwiseClose_of_isWarm_of_minorises`. Working setwise is what makes the counterexample
and the minorisation argument below finite: neither ever has to compute an `rnDeriv`. -/

/-- **`μ` minorises `ν` at rate `m`**: `m * ν S ≤ μ S` for every measurable `S`, i.e.
`m • ν ≤ μ`. The mirror image of `Arlib.IsWarm`. -/
def Minorises (m : ℝ≥0∞) (μ ν : Measure Ω) : Prop :=
  ∀ S : Set Ω, MeasurableSet S → m * ν S ≤ μ S

/-- Unfolding lemma for `Minorises`. -/
theorem minorises_iff (m : ℝ≥0∞) (μ ν : Measure Ω) :
    Minorises m μ ν ↔ ∀ S : Set Ω, MeasurableSet S → m * ν S ≤ μ S := Iff.rfl

/-- Minorisation is exactly domination in the other direction, `m • ν ≤ μ`. -/
theorem minorises_iff_smul_le {m : ℝ≥0∞} (μ ν : Measure Ω) :
    Minorises m μ ν ↔ m • ν ≤ μ := by
  rw [Measure.le_iff]
  exact forall_congr' fun S => forall_congr' fun _ => by
    rw [Measure.smul_apply, smul_eq_mul]

/-- **Every measure minorises itself at rate `1`.** -/
@[simp] theorem Minorises.refl (μ : Measure Ω) : Minorises 1 μ μ := by
  intro S _
  simp

/-- **A minorisation rate may always be weakened.** -/
theorem Minorises.mono {m m' : ℝ≥0∞} {μ ν : Measure Ω} (h : Minorises m μ ν) (hm : m' ≤ m) :
    Minorises m' μ ν := fun S hS => (by gcongr : m' * ν S ≤ m * ν S).trans (h S hS)

/-- Between probability measures the minorisation rate is at most `1`: take `S = univ`. -/
theorem Minorises.le_one {m : ℝ≥0∞} {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : Minorises m μ ν) : m ≤ 1 := by
  have := h univ MeasurableSet.univ
  simpa using this

/-- **Warmness implies absolute continuity.** If `ν S = 0` then `μ S ≤ M * 0 = 0`; note
this holds even at `M = ⊤`, since `⊤ * 0 = 0` in `ℝ≥0∞`. -/
theorem absolutelyContinuous_of_isWarm {M : ℝ≥0∞} {μ ν : Measure Ω} (h : IsWarm M μ ν) :
    μ ≪ ν :=
  Measure.AbsolutelyContinuous.mk fun S hS hνS => by
    simpa [hνS] using h S hS

/-! ### From the density bound to the setwise bound -/

/-- **A pointwise `ε`-bound is `(1 + ε)`-warmness.** Integrate the density bound over `S`,
using `μ S = ∫_S dμ/dν dν`. -/
theorem PointwiseClose.isWarm {μ ν : Measure Ω} {ε : ℝ≥0∞} [SigmaFinite μ] [SigmaFinite ν]
    (h : PointwiseClose μ ν ε) : IsWarm (1 + ε) μ ν := by
  intro S hS
  calc μ S = ∫⁻ x in S, μ.rnDeriv ν x ∂ν := (Measure.setLIntegral_rnDeriv h.1 S).symm
    _ ≤ ∫⁻ _ in S, (1 + ε) ∂ν := lintegral_mono_ae (ae_restrict_of_ae h.rnDeriv_le)
    _ = (1 + ε) * ν S := by rw [setLIntegral_const]

/-- **A pointwise `ε`-bound is a `(1 - ε)`-minorisation.** -/
theorem PointwiseClose.minorises {μ ν : Measure Ω} {ε : ℝ≥0∞} [SigmaFinite μ] [SigmaFinite ν]
    (h : PointwiseClose μ ν ε) : Minorises (1 - ε) μ ν := by
  intro S hS
  calc (1 - ε) * ν S = ∫⁻ _ in S, (1 - ε) ∂ν := by rw [setLIntegral_const]
    _ ≤ ∫⁻ x in S, μ.rnDeriv ν x ∂ν := lintegral_mono_ae (ae_restrict_of_ae h.le_rnDeriv)
    _ = μ S := Measure.setLIntegral_rnDeriv h.1 S

/-- The upper setwise bound, spelled out: `μ S ≤ (1 + ε) * ν S`. -/
theorem PointwiseClose.measure_le {μ ν : Measure Ω} {ε : ℝ≥0∞} [SigmaFinite μ] [SigmaFinite ν]
    (h : PointwiseClose μ ν ε) {S : Set Ω} (hS : MeasurableSet S) : μ S ≤ (1 + ε) * ν S :=
  h.isWarm S hS

/-- The lower setwise bound, spelled out: `(1 - ε) * ν S ≤ μ S`. -/
theorem PointwiseClose.le_measure {μ ν : Measure Ω} {ε : ℝ≥0∞} [SigmaFinite μ] [SigmaFinite ν]
    (h : PointwiseClose μ ν ε) {S : Set Ω} (hS : MeasurableSet S) : (1 - ε) * ν S ≤ μ S :=
  h.minorises S hS

/-! ### From the setwise bound to the density bound

The converse direction, which is what any *construction* of a pointwise-close law has to
go through: one bounds `μ S` against `ν S` setwise and then reads off the density. The
tool is `MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite`. -/

/-- **Warmness bounds the density above.** -/
theorem rnDeriv_le_of_isWarm {M : ℝ≥0∞} {μ ν : Measure Ω} [SigmaFinite ν]
    (h : IsWarm M μ ν) : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ M := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
    fun S hS _ => ?_
  rw [setLIntegral_const]
  exact (Measure.setLIntegral_rnDeriv_le S).trans (h S hS)

/-- **Minorisation bounds the density below.** Unlike the upper bound this needs `μ ≪ ν`:
without it the singular part of `μ` carries mass that the density does not see. -/
theorem le_rnDeriv_of_minorises {m : ℝ≥0∞} {μ ν : Measure Ω} [SigmaFinite μ] [SigmaFinite ν]
    (hac : μ ≪ ν) (h : Minorises m μ ν) : ∀ᵐ x ∂ν, m ≤ μ.rnDeriv ν x := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (f := fun _ => m) measurable_const
    fun S hS _ => ?_
  rw [setLIntegral_const, Measure.setLIntegral_rnDeriv hac S]
  exact h S hS

/-- **The two setwise bounds together are pointwise closeness.** This is the form in which
a pointwise-almost-uniform sampler gets *built*: establish `(1 - ε) * π S ≤ μ S ≤ (1 + ε) * π S`
for every measurable `S`, and the density bound follows. -/
theorem pointwiseClose_of_isWarm_of_minorises {μ ν : Measure Ω} {ε : ℝ≥0∞} [SigmaFinite μ]
    [SigmaFinite ν] (hw : IsWarm (1 + ε) μ ν) (hm : Minorises (1 - ε) μ ν) :
    PointwiseClose μ ν ε := by
  refine ⟨absolutelyContinuous_of_isWarm hw, ?_⟩
  filter_upwards [rnDeriv_le_of_isWarm hw,
      le_rnDeriv_of_minorises (absolutelyContinuous_of_isWarm hw) hm]
    with x h₁ h₂ using ⟨h₂, h₁⟩

/-- `PointwiseClose` is *equivalent* to the pair of setwise bounds. -/
theorem pointwiseClose_iff_isWarm_and_minorises {μ ν : Measure Ω} {ε : ℝ≥0∞} [SigmaFinite μ]
    [SigmaFinite ν] :
    PointwiseClose μ ν ε ↔ IsWarm (1 + ε) μ ν ∧ Minorises (1 - ε) μ ν :=
  ⟨fun h => ⟨h.isWarm, h.minorises⟩, fun h => pointwiseClose_of_isWarm_of_minorises h.1 h.2⟩

/-! ## Pointwise closeness implies a total variation bound, with the same constant -/

/-- **`PointwiseClose μ ν ε → TVLe μ ν ε`**, for probability measures, and the constant is
exactly `ε` with no loss.

Both halves come from the setwise form and `ν S ≤ 1`: the upper bound
`μ S ≤ (1 + ε) * ν S = ν S + ε * ν S ≤ ν S + ε`, and the lower bound
`(1 - ε) * ν S = ν S - ε * ν S ≤ μ S`, i.e. `ν S ≤ μ S + ε * ν S ≤ μ S + ε`.

The converse is **false**; see `Arlib.MarkovChains.exists_tvLe_not_pointwiseClose`. -/
theorem PointwiseClose.tvLe {μ ν : Measure Ω} {ε : ℝ≥0∞} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : PointwiseClose μ ν ε) : TVLe μ ν ε := by
  intro S hS
  have hεν : ε * ν S ≤ ε := by
    calc ε * ν S ≤ ε * 1 := by gcongr; exact prob_le_one
      _ = ε := mul_one ε
  refine ⟨?_, ?_⟩
  · calc μ S ≤ (1 + ε) * ν S := h.measure_le hS
      _ = ν S + ε * ν S := by rw [add_mul, one_mul]
      _ ≤ ν S + ε := by gcongr
  · have hlo : ν S - ε * ν S ≤ μ S := by
      have hle := h.le_measure hS
      rwa [ENNReal.sub_mul fun _ _ => measure_ne_top ν S, one_mul] at hle
    calc ν S ≤ ν S - ε * ν S + ε * ν S := le_tsub_add
      _ ≤ μ S + ε := by gcongr

/-! ## The two-point family, and the failure of the converse

Everything the counterexample needs lives on `Bool`. `twoPoint p` is the law with mass `p`
on `true` and `1 - p` on `false`; the whole of the counterexample is that `twoPoint p` and
`twoPoint q` are at total variation distance `|p - q|`, which is small when `p` and `q` are
both small, while their *ratio* at `true` is `p / q`, which is not. -/

/-- The two-point law on `Bool` with mass `p` on `true`. -/
noncomputable def twoPoint (p : ℝ≥0∞) : Measure Bool :=
  (1 - p) • Measure.dirac false + p • Measure.dirac true

/-- Evaluation of `twoPoint` on an arbitrary set. -/
theorem twoPoint_apply (p : ℝ≥0∞) (S : Set Bool) :
    twoPoint p S = (1 - p) * S.indicator 1 false + p * S.indicator 1 true := by
  simp [twoPoint]

@[simp] theorem twoPoint_apply_true (p : ℝ≥0∞) : twoPoint p {true} = p := by
  simp [twoPoint_apply]

@[simp] theorem twoPoint_apply_false (p : ℝ≥0∞) : twoPoint p {false} = 1 - p := by
  simp [twoPoint_apply]

/-- `twoPoint p` is a probability measure exactly when `p ≤ 1`. -/
theorem isProbabilityMeasure_twoPoint {p : ℝ≥0∞} (hp : p ≤ 1) :
    IsProbabilityMeasure (twoPoint p) := by
  constructor
  rw [twoPoint_apply]
  simp [tsub_add_cancel_of_le hp]

/-- **The two-point laws are at total variation distance `q - p`.**  Four cases, one per
subset of `Bool`. -/
theorem tvLe_twoPoint {p q : ℝ≥0∞} (hq : q ≤ 1) (hpq : p ≤ q) :
    TVLe (twoPoint p) (twoPoint q) (q - p) := by
  have hp : p ≤ 1 := hpq.trans hq
  intro S _
  rw [twoPoint_apply, twoPoint_apply]
  by_cases hf : false ∈ S <;> by_cases ht : true ∈ S <;>
    simp only [Set.indicator_of_mem, Set.indicator_of_notMem, hf, ht, Pi.one_apply,
      mul_one, mul_zero, add_zero, zero_add, not_false_eq_true]
  · -- both points: total mass `1` on each side
    rw [tsub_add_cancel_of_le hp, tsub_add_cancel_of_le hq]
    exact ⟨le_self_add, le_self_add⟩
  · -- `false` only
    refine ⟨?_, le_add_right (tsub_le_tsub_left hpq 1)⟩
    rw [tsub_add_tsub_cancel hq hpq]
  · -- `true` only
    exact ⟨le_add_right hpq, by rw [add_tsub_cancel_of_le hpq]⟩
  · -- neither point
    simp

/-- `twoPoint p` is absolutely continuous with respect to `twoPoint q` whenever `twoPoint q`
has full support, i.e. `0 < q < 1`. -/
theorem absolutelyContinuous_twoPoint {p q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : q < 1) :
    twoPoint p ≪ twoPoint q := by
  refine Measure.AbsolutelyContinuous.mk fun S _ hS => ?_
  rw [twoPoint_apply] at hS ⊢
  rw [add_eq_zero] at hS
  obtain ⟨h1, h2⟩ := hS
  have hb : S.indicator (1 : Bool → ℝ≥0∞) false = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h (tsub_pos_of_lt hq1).ne'
    · exact h
  have ht : S.indicator (1 : Bool → ℝ≥0∞) true = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hq0
    · exact h
  rw [hb, ht, mul_zero, mul_zero, add_zero]

/-! ### The counterexample

Two distinct failures, both at total variation distance at most `δ` for `δ` as small as one
likes. They are genuinely different, and both matter for `AUDIT-KV97.md` §4b.

**Failure 1 — no density at all.**  `twoPoint δ` puts mass `δ` on `true`; `twoPoint 0` puts
none. So `twoPoint δ` is not absolutely continuous with respect to `twoPoint 0`, and
`PointwiseClose (twoPoint δ) (twoPoint 0) ε` is false for **every** `ε`, `ε = ⊤` included.
A chain that has mixed to within `δ` in total variation may still put mass where the target
puts none; a mixing bound says nothing about that.

**Failure 2 — a density, but an unbounded ratio.**  `twoPoint δ` against `twoPoint (δ * δ)`:
absolute continuity now holds, the total variation distance is `δ - δ² ≤ δ`, but the density
at `true` is `δ / δ² = 1/δ`.  So for any prescribed `ε`, however large, taking `δ` with
`(1 + ε) * δ < 1` produces two probability measures at total variation distance `≤ δ` that
are not pointwise `ε`-close. -/

/-- **Failure 1**: `twoPoint δ` has no density with respect to `twoPoint 0` at all. -/
theorem not_pointwiseClose_twoPoint_zero {δ ε : ℝ≥0∞} (hδ : δ ≠ 0) :
    ¬ PointwiseClose (twoPoint δ) (twoPoint 0) ε := by
  rintro ⟨hac, -⟩
  have h0 : twoPoint (0 : ℝ≥0∞) {true} = 0 := by simp
  have h1 : twoPoint δ {true} = 0 := hac h0
  rw [twoPoint_apply_true] at h1
  exact hδ h1

/-- If `(1 + ε) * δ < 1` then in particular `δ < 1`. -/
theorem lt_one_of_one_add_mul_lt_one {δ ε : ℝ≥0∞} (hδε : (1 + ε) * δ < 1) : δ < 1 := by
  refine lt_of_le_of_lt ?_ hδε
  calc δ = 1 * δ := (one_mul δ).symm
    _ ≤ (1 + ε) * δ := by gcongr; exact le_self_add

/-- The square of an element below `1` is below `1`. -/
theorem mul_self_lt_one {δ : ℝ≥0∞} (hδ1 : δ < 1) : δ * δ < 1 :=
  calc δ * δ ≤ 1 * δ := by gcongr
    _ = δ := one_mul δ
    _ < 1 := hδ1

/-- **Failure 2**: the density exists but its value at `true` is `1/δ`, so no pointwise
bound `ε` with `(1 + ε) * δ < 1` can hold. -/
theorem not_pointwiseClose_twoPoint_sq {δ ε : ℝ≥0∞} (hδ0 : δ ≠ 0) (hδε : (1 + ε) * δ < 1) :
    ¬ PointwiseClose (twoPoint δ) (twoPoint (δ * δ)) ε := by
  have hδ1 : δ < 1 := lt_one_of_one_add_mul_lt_one hδε
  have hδt : δ ≠ ⊤ := hδ1.ne_top
  haveI := isProbabilityMeasure_twoPoint hδ1.le
  haveI := isProbabilityMeasure_twoPoint (mul_self_lt_one hδ1).le
  intro hpc
  have hle := hpc.measure_le (measurableSet_singleton true)
  rw [twoPoint_apply_true, twoPoint_apply_true, ← mul_assoc] at hle
  have hlt : (1 + ε) * δ * δ < δ := by
    calc (1 + ε) * δ * δ < 1 * δ := by
          exact ENNReal.mul_lt_mul_left hδ0 hδt hδε
      _ = δ := one_mul δ
  exact absurd hle (not_le.2 hlt)

/-- **The converse of `PointwiseClose.tvLe` fails, and fails as badly as possible.**

For every `δ ≠ 0` there are two probability measures on `Bool` at total variation distance
at most `δ` which are **not** pointwise `ε`-close for **any** `ε` — not even `ε = ⊤`.

This is the formal content of `AUDIT-KV97.md` §4b: a mixing-time bound produces a `TVLe`,
and no amount of mixing, by itself, produces a `PointwiseClose`. -/
theorem exists_tvLe_not_pointwiseClose_forall {δ : ℝ≥0∞} (hδ0 : δ ≠ 0) (hδ1 : δ ≤ 1) :
    ∃ μ ν : Measure Bool, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      TVLe μ ν δ ∧ ∀ ε : ℝ≥0∞, ¬ PointwiseClose μ ν ε := by
  refine ⟨twoPoint δ, twoPoint 0, isProbabilityMeasure_twoPoint hδ1,
    isProbabilityMeasure_twoPoint zero_le_one, ?_,
    fun _ => not_pointwiseClose_twoPoint_zero hδ0⟩
  simpa using (tvLe_twoPoint hδ1 (show (0 : ℝ≥0∞) ≤ δ by simp)).symm

/-- **The converse fails even under absolute continuity.**  Given any target tolerance `ε`,
choose `δ` with `(1 + ε) * δ < 1`: there are then two probability measures with
`μ ≪ ν`, at total variation distance at most `δ`, that are not pointwise `ε`-close.

So the failure is not an artefact of `PointwiseClose` demanding a density: it is the density
*ratio* that a total variation bound fails to control. -/
theorem exists_tvLe_not_pointwiseClose {δ ε : ℝ≥0∞} (hδ0 : δ ≠ 0) (hδε : (1 + ε) * δ < 1) :
    ∃ μ ν : Measure Bool, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      μ ≪ ν ∧ TVLe μ ν δ ∧ ¬ PointwiseClose μ ν ε := by
  have hδ1 : δ < 1 := lt_one_of_one_add_mul_lt_one hδε
  have hsq : δ * δ < 1 := mul_self_lt_one hδ1
  refine ⟨twoPoint δ, twoPoint (δ * δ), isProbabilityMeasure_twoPoint hδ1.le,
    isProbabilityMeasure_twoPoint hsq.le,
    absolutelyContinuous_twoPoint (mul_ne_zero hδ0 hδ0) hsq, ?_,
    not_pointwiseClose_twoPoint_sq hδ0 hδε⟩
  refine TVLe.mono ((tvLe_twoPoint hδ1.le ?_).symm) tsub_le_self
  calc δ * δ ≤ 1 * δ := by gcongr
    _ = δ := one_mul δ

/-- **No function converts a total variation bound into a pointwise bound.**  Fix any
tolerance `δ ≠ 0` on the total variation distance.  There is no `ε` — not even `⊤` — such
that `TVLe μ ν δ` implies `PointwiseClose μ ν ε` for all probability measures `μ`, `ν`.

Stated as the non-existence of the conversion function, which is the shape in which a
downstream development would want to use it: "run the chain until the total variation error
is `δ`, then quote a pointwise error `f δ`". No such `f` exists. -/
theorem not_exists_pointwiseClose_of_tvLe {δ : ℝ≥0∞} (hδ0 : δ ≠ 0) (hδ1 : δ ≤ 1) :
    ¬ ∃ ε : ℝ≥0∞, ∀ μ ν : Measure Bool, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        TVLe μ ν δ → PointwiseClose μ ν ε := by
  rintro ⟨ε, hε⟩
  obtain ⟨μ, ν, hμ, hν, htv, hno⟩ := exists_tvLe_not_pointwiseClose_forall hδ0 hδ1
  exact hno ε (hε μ ν hμ hν htv)

/-! ## A sufficient extra hypothesis: uniform minorisation

The counterexample above says a mixing bound alone can never give a pointwise bound.  What
*does* work is the classical Doeblin condition: the kernel puts a fixed fraction `c` of the
stationary measure everywhere, in one step.  Under it the chain's density is squeezed
between two constants that converge to `1` geometrically, so the chain becomes pointwise
`ε`-close for `t` large — and the rate is governed by `c`, not by any conductance. -/

/-- **Uniform minorisation (Doeblin's condition)**: from *every* state the kernel already
covers a `c`-fraction of the stationary measure,

  `∀ x, ∀ measurable S, c * pi S ≤ P x S`.

Equivalently `c • pi ≤ P x` for every `x`. -/
def UniformMinorisation (P : Kernel Ω Ω) (pi : Measure Ω) (c : ℝ≥0∞) : Prop :=
  ∀ x : Ω, Minorises c (P x) pi

/-- Unfolding lemma for `UniformMinorisation`. -/
theorem uniformMinorisation_iff (P : Kernel Ω Ω) (pi : Measure Ω) (c : ℝ≥0∞) :
    UniformMinorisation P pi c ↔ ∀ x : Ω, ∀ S : Set Ω, MeasurableSet S → c * pi S ≤ P x S :=
  Iff.rfl

/-- A Markov kernel cannot be minorised at a rate above `1`: take `S = univ`. -/
theorem UniformMinorisation.le_one {P : Kernel Ω Ω} {pi : Measure Ω} {c : ℝ≥0∞}
    [IsMarkovKernel P] [IsProbabilityMeasure pi] [Nonempty Ω]
    (h : UniformMinorisation P pi c) : c ≤ 1 := by
  have := h (Classical.arbitrary Ω) Set.univ MeasurableSet.univ
  simpa using this

/-- **The minorised decomposition of one step.**  Split `P x S` as the guaranteed floor
`c * pi S` plus the excess `P x S - c * pi S`; the floor integrates to itself because `μ` is
a probability measure.  Both propagation lemmas below are this identity plus a bound on the
excess. -/
theorem step_apply_eq_add_lintegral {P : Kernel Ω Ω} {pi : Measure Ω} {c : ℝ≥0∞}
    (hmin : UniformMinorisation P pi c) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) :
    step P μ S = c * pi S + ∫⁻ x, (P x S - c * pi S) ∂μ := by
  rw [step_apply P μ hS]
  calc ∫⁻ x, P x S ∂μ = ∫⁻ x, (c * pi S + (P x S - c * pi S)) ∂μ :=
        lintegral_congr fun x => (add_tsub_cancel_of_le (hmin x S hS)).symm
    _ = c * pi S * μ Set.univ + ∫⁻ x, (P x S - c * pi S) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ = c * pi S + ∫⁻ x, (P x S - c * pi S) ∂μ := by rw [measure_univ, mul_one]

/-- **The excess integrates, against the stationary measure, to `(1 - c) * pi S`.**  This is
where invariance of `pi` enters, and it is the source of the contraction factor `1 - c`. -/
theorem lintegral_excess_pi {P : Kernel Ω Ω} {pi : Measure Ω} {c : ℝ≥0∞}
    [IsProbabilityMeasure pi] (hmin : UniformMinorisation P pi c) (hc : c ≤ 1)
    (hinv : step P pi = pi) {S : Set Ω} (hS : MeasurableSet S) :
    ∫⁻ x, (P x S - c * pi S) ∂pi = (1 - c) * pi S := by
  have hfin : ∫⁻ _ : Ω, c * pi S ∂pi ≠ ⊤ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact (ENNReal.mul_lt_top (hc.trans_lt ENNReal.one_lt_top) (measure_lt_top pi S)).ne
  have hle : (fun _ : Ω => c * pi S) ≤ᵐ[pi] fun x => P x S :=
    Filter.Eventually.of_forall fun x => hmin x S hS
  rw [lintegral_sub measurable_const hfin hle, lintegral_const, measure_univ, mul_one,
    ← step_apply P pi hS, hinv, ENNReal.sub_mul fun _ _ => measure_ne_top pi S, one_mul]

/-! ### One step contracts both bounds towards `1`

Both propagation lemmas have the same shape: `step P μ S = c * pi S + (excess)`, and the
excess against `μ` is sandwiched by the excess against `pi` times the current bound.  So a
bound `b` at time `t` becomes `c + b * (1 - c)` at time `t + 1` — an affine map with
fixed point `1` and contraction factor `1 - c`, *in both directions*. -/

/-- **One step, upper bound.**  An `M`-warm law becomes `(c + M * (1 - c))`-warm.  Since
`c + M * (1 - c) - 1 = (M - 1) * (1 - c)`, the warmness *excess* shrinks by `1 - c`. -/
theorem isWarm_step_of_uniformMinorisation {P : Kernel Ω Ω} {pi μ : Measure Ω} {c M : ℝ≥0∞}
    [IsProbabilityMeasure pi] [IsProbabilityMeasure μ]
    (hmin : UniformMinorisation P pi c) (hc : c ≤ 1) (hinv : step P pi = pi)
    (hw : IsWarm M μ pi) : IsWarm (c + M * (1 - c)) (step P μ) pi := by
  intro S hS
  rw [step_apply_eq_add_lintegral hmin μ hS]
  have hle : ∫⁻ x, (P x S - c * pi S) ∂μ ≤ M * ((1 - c) * pi S) := by
    have hsmul : μ ≤ M • pi := (isWarm_iff_le_smul _ _).1 hw
    calc ∫⁻ x, (P x S - c * pi S) ∂μ ≤ ∫⁻ x, (P x S - c * pi S) ∂(M • pi) :=
          lintegral_mono' hsmul le_rfl
      _ = M * ∫⁻ x, (P x S - c * pi S) ∂pi := lintegral_smul_measure _ _
      _ = M * ((1 - c) * pi S) := by rw [lintegral_excess_pi hmin hc hinv hS]
  calc c * pi S + ∫⁻ x, (P x S - c * pi S) ∂μ ≤ c * pi S + M * ((1 - c) * pi S) := by gcongr
    _ = (c + M * (1 - c)) * pi S := by ring

/-- **One step, lower bound.**  A law minorising `pi` at rate `m` comes out minorising it at
rate `c + m * (1 - c)`.  Applied at `m = 0` this says a single step already gives rate `c`,
from *any* start. -/
theorem minorises_step_of_uniformMinorisation {P : Kernel Ω Ω} {pi μ : Measure Ω} {c m : ℝ≥0∞}
    [IsProbabilityMeasure pi] [IsProbabilityMeasure μ]
    (hmin : UniformMinorisation P pi c) (hc : c ≤ 1) (hinv : step P pi = pi)
    (hm : Minorises m μ pi) : Minorises (c + m * (1 - c)) (step P μ) pi := by
  intro S hS
  rw [step_apply_eq_add_lintegral hmin μ hS]
  have hle : m * ((1 - c) * pi S) ≤ ∫⁻ x, (P x S - c * pi S) ∂μ := by
    have hsmul : m • pi ≤ μ := (minorises_iff_smul_le _ _).1 hm
    calc m * ((1 - c) * pi S) = m * ∫⁻ x, (P x S - c * pi S) ∂pi := by
          rw [lintegral_excess_pi hmin hc hinv hS]
      _ = ∫⁻ x, (P x S - c * pi S) ∂(m • pi) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ x, (P x S - c * pi S) ∂μ := lintegral_mono' hsmul le_rfl
  calc (c + m * (1 - c)) * pi S = c * pi S + m * ((1 - c) * pi S) := by ring
    _ ≤ c * pi S + ∫⁻ x, (P x S - c * pi S) ∂μ := by gcongr

/-! ### Iterating: the density is squeezed geometrically

The affine recursion `b ↦ c + b * (1 - c)` has closed form `1 + (1 - c)^t * (b₀ - 1)` above
and `1 - (1 - c)^t` below.  Both converge to `1` at rate `1 - c`. -/

/-- **The warmness parameter decays geometrically**: `M ↦ 1 + (1 - c)^t * (M - 1)`. -/
theorem isWarm_iterate_of_uniformMinorisation {P : Kernel Ω Ω} {pi μ : Measure Ω} {c M : ℝ≥0∞}
    [IsMarkovKernel P] [IsProbabilityMeasure pi] [IsProbabilityMeasure μ]
    (hmin : UniformMinorisation P pi c) (hc : c ≤ 1) (hinv : step P pi = pi)
    (hw : IsWarm M μ pi) (t : ℕ) :
    IsWarm (1 + (1 - c) ^ t * (M - 1)) (iterate P μ t) pi := by
  induction t with
  | zero =>
    rw [iterate_zero, pow_zero, one_mul, add_tsub_cancel_of_le (IsWarm.one_le hw)]
    exact hw
  | succ t ih =>
    have key : c + (1 + (1 - c) ^ t * (M - 1)) * (1 - c)
        = 1 + (1 - c) ^ (t + 1) * (M - 1) := by
      rw [add_mul, one_mul, ← add_assoc, add_tsub_cancel_of_le hc, pow_succ]
      ring
    rw [iterate_succ, ← key]
    exact isWarm_step_of_uniformMinorisation hmin hc hinv ih

/-- **The minorisation rate rises geometrically to `1`**: after `t` steps the chain
dominates `(1 - (1 - c)^t) • pi`, from *any* start.  No warmness hypothesis is needed for
this half — the floor is manufactured by the kernel. -/
theorem minorises_iterate_of_uniformMinorisation {P : Kernel Ω Ω} {pi μ : Measure Ω}
    {c : ℝ≥0∞} [IsMarkovKernel P] [IsProbabilityMeasure pi] [IsProbabilityMeasure μ]
    (hmin : UniformMinorisation P pi c) (hc : c ≤ 1) (hinv : step P pi = pi) (t : ℕ) :
    Minorises (1 - (1 - c) ^ t) (iterate P μ t) pi := by
  have hd1 : (1 : ℝ≥0∞) - c ≤ 1 := tsub_le_self
  have hdtop : (1 : ℝ≥0∞) - c ≠ ⊤ := (hd1.trans_lt ENNReal.one_lt_top).ne
  induction t with
  | zero =>
    rw [iterate_zero, pow_zero, tsub_self]
    intro S _
    simp
  | succ t ih =>
    have hdt : ((1 : ℝ≥0∞) - c) ^ t ≤ 1 := pow_le_one' hd1 t
    have hpow : ((1 : ℝ≥0∞) - c) ^ (t + 1) ≤ 1 - c := by
      rw [pow_succ]
      calc ((1 : ℝ≥0∞) - c) ^ t * (1 - c) ≤ 1 * (1 - c) := by gcongr
        _ = 1 - c := one_mul _
    have hmulsub : (1 - (1 - c) ^ t) * (1 - c) = (1 - c) - (1 - c) ^ (t + 1) := by
      rw [ENNReal.sub_mul fun _ _ => hdtop, one_mul, pow_succ]
    have key : c + (1 - (1 - c) ^ t) * (1 - c) = 1 - (1 - c) ^ (t + 1) := by
      rw [hmulsub]
      refine ENNReal.eq_sub_of_add_eq ((hpow.trans hd1).trans_lt ENNReal.one_lt_top).ne ?_
      rw [add_assoc, tsub_add_cancel_of_le hpow, add_tsub_cancel_of_le hc]
    rw [iterate_succ, ← key]
    exact minorises_step_of_uniformMinorisation hmin hc hinv ih

/-! ### The conclusion: a pointwise-almost-uniform sampler, under minorisation -/

/-- **Under uniform minorisation, a warm start becomes pointwise `ε`-close.**  The two
hypotheses on `t` are exactly the two geometric bounds; `eventually_pointwiseClose_iterate`
below shows they hold for all large `t` once `0 < c` and `M < ⊤`.

Note what carries the argument: the rate is `1 - c`, a property of the *kernel*, and no
conductance, isoperimetry or spectral gap appears anywhere. -/
theorem pointwiseClose_iterate_of_uniformMinorisation {P : Kernel Ω Ω} {pi μ : Measure Ω}
    {c M ε : ℝ≥0∞} [IsMarkovKernel P] [IsProbabilityMeasure pi] [IsProbabilityMeasure μ]
    (hmin : UniformMinorisation P pi c) (hc : c ≤ 1) (hinv : step P pi = pi)
    (hw : IsWarm M μ pi) {t : ℕ} (h₁ : (1 - c) ^ t ≤ ε) (h₂ : (1 - c) ^ t * (M - 1) ≤ ε) :
    PointwiseClose (iterate P μ t) pi ε :=
  pointwiseClose_of_isWarm_of_minorises
    (IsWarm.mono (isWarm_iterate_of_uniformMinorisation hmin hc hinv hw t)
      (add_le_add le_rfl h₂))
    (Minorises.mono (minorises_iterate_of_uniformMinorisation hmin hc hinv t)
      (tsub_le_tsub_left h₁ 1))

/-- **Explicitly: for all large `t`.**  With a genuine minorisation rate `0 < c` and a
finite warmness `M`, the chain is pointwise `ε`-close to `pi` for every `t` beyond an
explicit threshold — the first `t` with `(1 - c)^t * max 1 (M - 1) < ε`, i.e.
`t ≥ log(max 1 (M-1) / ε) / log(1/(1-c))`. -/
theorem eventually_pointwiseClose_iterate {P : Kernel Ω Ω} {pi μ : Measure Ω} {c M ε : ℝ≥0∞}
    [IsMarkovKernel P] [IsProbabilityMeasure pi] [IsProbabilityMeasure μ]
    (hmin : UniformMinorisation P pi c) (hc : c ≤ 1) (hc0 : c ≠ 0) (hinv : step P pi = pi)
    (hw : IsWarm M μ pi) (hM : M ≠ ⊤) (hε : ε ≠ 0) :
    ∀ᶠ t in atTop, PointwiseClose (iterate P μ t) pi ε := by
  have hd1 : (1 : ℝ≥0∞) - c < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc0
  have hK1 : (1 : ℝ≥0∞) ≤ max 1 (M - 1) := le_max_left _ _
  have hKtop : max 1 (M - 1) ≠ ⊤ :=
    (max_lt ENNReal.one_lt_top (tsub_le_self.trans_lt hM.lt_top)).ne
  have htend : Tendsto (fun t : ℕ => (1 - c) ^ t * max 1 (M - 1)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun t : ℕ => ((1 : ℝ≥0∞) - c) ^ t) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hd1
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hKtop)
  filter_upwards [htend.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))] with t ht
  refine pointwiseClose_iterate_of_uniformMinorisation hmin hc hinv hw ?_ ?_
  · refine le_of_lt (lt_of_le_of_lt ?_ ht)
    calc ((1 : ℝ≥0∞) - c) ^ t = (1 - c) ^ t * 1 := (mul_one _).symm
      _ ≤ (1 - c) ^ t * max 1 (M - 1) := by gcongr
  · exact le_of_lt (lt_of_le_of_lt (by gcongr; exact le_max_right _ _) ht)

/-! ## Non-vacuity: the instantly mixing kernel

`CLAUDE.md` §11.  `Kernel.const Ω pi` — resample from `pi` at every step — satisfies
`UniformMinorisation` at the best possible rate `c = 1`, and reaches `PointwiseClose … 0`
in one step.  So neither `Arlib.MarkovChains.UniformMinorisation` nor
`Arlib.MarkovChains.PointwiseClose` is a predicate nothing satisfies, and the hypothesis of
`pointwiseClose_iterate_of_uniformMinorisation` is satisfiable at its extreme value. -/

/-- **The instantly mixing kernel is uniformly minorised at rate `1`.** -/
theorem uniformMinorisation_const (pi : Measure Ω) :
    UniformMinorisation (Kernel.const Ω pi) pi 1 := by
  intro x S _
  simp

/-- **And it reaches pointwise closeness with error `0`, in one step, from any start.** -/
theorem pointwiseClose_iterate_const (pi μ₀ : Measure Ω) [IsProbabilityMeasure pi]
    [IsProbabilityMeasure μ₀] :
    PointwiseClose (iterate (Kernel.const Ω pi) μ₀ 1) pi 0 := by
  rw [iterate_one, step_const_eq]
  exact pointwiseClose_self pi

/-- **The non-vacuity witness, packaged.**  One concrete chain on `Bool` is simultaneously
uniformly minorised at rate `1`, stationary, `MixesWithin _ _ _ 1 0`, and
`PointwiseClose _ _ 0` after one step.  The last two are the point: the same chain
witnesses both the total-variation predicate and the strictly stronger pointwise one. -/
theorem exists_uniformMinorisation_and_pointwiseClose :
    ∃ (Om : Type) (_ : MeasurableSpace Om) (P : Kernel Om Om) (pi μ₀ : Measure Om),
      IsMarkovKernel P ∧ IsProbabilityMeasure pi ∧ IsProbabilityMeasure μ₀ ∧
        UniformMinorisation P pi 1 ∧ step P pi = pi ∧ MixesWithin P pi μ₀ 1 0 ∧
        PointwiseClose (iterate P μ₀ 1) pi 0 :=
  ⟨Bool, inferInstance, Kernel.const Bool (Measure.dirac true), Measure.dirac true,
    Measure.dirac false, inferInstance, inferInstance, inferInstance,
    uniformMinorisation_const _, step_const_eq _ _, mixesWithin_const _ _,
    pointwiseClose_iterate_const _ _⟩

/-! ## Why uniform minorisation is the wrong hypothesis for a local walk

Uniform minorisation is a *global* condition: in **one** step, from **every** state, the
kernel must already spread a fixed fraction of `pi` over the whole space.  A local walk —
one that moves at most `δ` — cannot do this on a body of diameter greater than `δ`, and the
obstruction has nothing to do with the boundary.  The two lemmas below are that obstruction,
stated abstractly; see the module docstring for what they say about `Arlib.MarkovChains.ballWalk`. -/

/-- **Uniform minorisation forces the kernel's support to be everything.**  If the chain
cannot reach `S` from `x` in one step, then `S` is `pi`-null. -/
theorem measure_eq_zero_of_uniformMinorisation {P : Kernel Ω Ω} {pi : Measure Ω} {c : ℝ≥0∞}
    (h : UniformMinorisation P pi c) (hc : c ≠ 0) {x : Ω} {S : Set Ω} (hS : MeasurableSet S)
    (hPx : P x S = 0) : pi S = 0 := by
  have hle : c * pi S ≤ 0 := hPx ▸ h x S hS
  rcases mul_eq_zero.1 (le_antisymm hle (by simp)) with hc0 | hpi
  · exact absurd hc0 hc
  · exact hpi

/-- **One unreachable set of positive stationary measure kills every minorisation rate.**
This is exactly the ball walk's situation: for `x ∈ K` and `S ⊆ K` a chunk of `K` at
distance more than `δ` from `x`, one step of the walk reaches `S` with probability `0`,
while `S` carries positive uniform measure. -/
theorem not_uniformMinorisation_of_unreachable {P : Kernel Ω Ω} {pi : Measure Ω} {c : ℝ≥0∞}
    (hc : c ≠ 0) {x : Ω} {S : Set Ω} (hS : MeasurableSet S) (hPx : P x S = 0)
    (hpi : pi S ≠ 0) : ¬ UniformMinorisation P pi c :=
  fun h => hpi (measure_eq_zero_of_uniformMinorisation h hc hS hPx)

/-- **The bridge back to the total-variation interface.**  A pointwise bound is strictly
more than a mixing bound, so it always implies one, with the same constant. -/
theorem mixesWithin_of_pointwiseClose {P : Kernel Ω Ω} {pi μ₀ : Measure Ω} {t : ℕ} {ε : ℝ≥0∞}
    [IsMarkovKernel P] [IsProbabilityMeasure pi] [IsProbabilityMeasure μ₀]
    (h : PointwiseClose (iterate P μ₀ t) pi ε) : MixesWithin P pi μ₀ t ε :=
  h.tvLe

end Arlib.MarkovChains
