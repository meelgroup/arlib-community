/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Total variation distance in bounded-predicate form

A sampler for a continuous distribution — a ball walk on a convex body, hit-and-run,
Metropolis on `ℝⁿ` — never returns an exact draw from its target. It returns a draw from
whatever law the chain has reached after finitely many steps. Every downstream statement
about such a sampler is therefore a statement about a measure that is merely *close* to
the target, and "close" has to mean something. Total variation distance is what it means:
it is the notion under which a bound on the sampler transfers, with no loss, to a bound on
the probability of **any** measurable event the caller cares about, and — the headline of
this file — to a bound on the expectation of **any** `[0,1]`-valued observable.

Mathlib v4.32 has no total variation API for measures: the only `totalVariation` in the
library is the Jordan decomposition of a *signed* measure, from which one could extract
`‖μ - ν‖` at the cost of dragging signed measures through every statement. This file avoids
that entirely.

## The bounded form

The distance is not defined. What is defined is the predicate

  `TVLe μ ν ε  ↔  ∀ measurable S, μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε`,

read as "the total variation distance between `μ` and `ν` is at most `ε`". This is the form
every consumer wants — nobody uses the exact distance, they use a bound on it — and carrying
the bound rather than a `sSup` means no supremum bookkeeping: no `le_csSup` side conditions,
no nonemptiness hypotheses, and the pseudometric laws below are one-line consequences of
`add_le_add` instead of arguments about suprema.

Everything is valued in `ℝ≥0∞`, so `ε = ⊤` is allowed and is vacuously true (`tvLe_top`),
and the triangle inequality needs no finiteness hypothesis.

Note the convention: `TVLe μ ν ε` bounds the *unnormalised* quantity `sup_S |μ S - ν S|`,
which for probability measures is **half** the `L¹` distance.

## Main definitions

* `Arlib.TVLe` — `μ` and `ν` are within total variation distance `ε`.
* `Arlib.IsWarm` — `μ` is `M`-warm with respect to `ν`, i.e. `μ S ≤ M * ν S` setwise.

## Main results

* `Arlib.TVLe.measure_le_add` — the transfer lemma for events: a bound on an event under
  `ν` becomes a bound under `μ`, degraded by exactly `ε`.
* `Arlib.TVLe.integral_le` — **the headline.** The transfer lemma for *observables*: for
  probability measures and any measurable `f : Ω → ℝ` with `0 ≤ f ≤ 1`,
  `|∫ f ∂μ − ∫ f ∂ν| ≤ ε.toReal`. Proved by the layer-cake representation
  `∫ f = ∫_{(0,1]} μ {f ≥ t} dt` and `measure_le_add` pointwise in `t`.
* `Arlib.TVLe.refl`, `Arlib.TVLe.symm`, `Arlib.TVLe.trans`, `Arlib.TVLe.mono` — the
  pseudometric laws.
* `Arlib.TVLe.eq_of_zero` — `TVLe μ ν 0` forces `μ = ν`, so the pseudometric separates
  points.
* `Arlib.tvLe_of_forall_le` — for probability measures the one-sided bound already gives
  the two-sided one, by complementation.
* `Arlib.TVLe.map` — the deterministic data-processing inequality.
* `Arlib.IsWarm.tvLe` — warmness `M` implies `TVLe (M - 1)` for probability measures.

## Scope

This file is deliberately thin. There is no `sSup` definition of the distance itself, no
coupling characterisation, no Pinsker inequality, and no link to a density or to the Jordan
decomposition. Nothing here converts a spectral gap or a conductance bound into a `TVLe`;
that is the theorem this file is the target of, not a theorem it contains.

The **kernel** data-processing inequality is not here either, but it is *not* missing from
the library — this paragraph used to say it was, and that was wrong long enough to mislead a
reader. It is proved twice, downstream:

* `Arlib.tvLe_step` / `Arlib.tvLe_iterate` (`Arlib/MarkovChains/Continuous/Warmness.lean:293`,
  `:302`), resting on `Arlib.lintegral_le_of_tvLe` (`:241`), which runs the layer cake
  directly in `ℝ≥0∞`. **This is the strong form**: no `IsProbabilityMeasure`, no `ε ≠ ⊤`.
  Prefer it.
* `Arlib.TVLe.bind` (`Arlib/Probability/TVKernel.lean`), reached instead through the
  real-valued `TVLe.integral_le` below, and so carrying both of those hypotheses. It exists
  only because it lives in this layer, which cannot see `Arlib.MarkovChains`.

The absence of the *coupling* characterisation, by contrast, is real and load-bearing: it is
why the phase composition in `Arlib/Convexity/GaussianCooling/PhaseInduction.lean` accumulates
error geometrically where Cousins–Vempala accumulate it additively. See `AUDIT.md` §0o.
-/

namespace Arlib

open MeasureTheory Set
open scoped ENNReal

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ ν ξ : Measure Ω} {ε ε' δ p : ℝ≥0∞} {S : Set Ω}

/-- **The total variation distance between `μ` and `ν` is at most `ε`**: every measurable
event has almost the same mass under the two measures, with slack `ε`,

  `∀ measurable S, μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε`.

Stated as a bound rather than as an exact distance, because a bound is what every consumer
of a sampler uses and because it avoids a supremum. See the module docstring. -/
def TVLe (μ ν : Measure Ω) (ε : ℝ≥0∞) : Prop :=
  ∀ S : Set Ω, MeasurableSet S → μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε

/-- Unfolding lemma for `TVLe`, so that callers need not `rw [TVLe]`. -/
theorem tvLe_iff (μ ν : Measure Ω) (ε : ℝ≥0∞) :
    TVLe μ ν ε ↔ ∀ S : Set Ω, MeasurableSet S → μ S ≤ ν S + ε ∧ ν S ≤ μ S + ε := Iff.rfl

/-- The left half of the bound: `μ S ≤ ν S + ε`. -/
theorem TVLe.left (h : TVLe μ ν ε) (hS : MeasurableSet S) : μ S ≤ ν S + ε := (h S hS).1

/-- The right half of the bound: `ν S ≤ μ S + ε`. -/
theorem TVLe.right (h : TVLe μ ν ε) (hS : MeasurableSet S) : ν S ≤ μ S + ε := (h S hS).2

/-! ## The pseudometric laws -/

/-- **A measure is at distance zero from itself.** -/
@[simp] theorem TVLe.refl (μ : Measure Ω) : TVLe μ μ 0 := by
  intro S _
  simp

/-- **Symmetry.** -/
theorem TVLe.symm (h : TVLe μ ν ε) : TVLe ν μ ε := fun S hS => ⟨(h S hS).2, (h S hS).1⟩

/-- `TVLe` is a symmetric relation, in `Iff` form. -/
theorem tvLe_comm : TVLe μ ν ε ↔ TVLe ν μ ε := ⟨TVLe.symm, TVLe.symm⟩

/-- **A bound may always be weakened.** -/
theorem TVLe.mono (h : TVLe μ ν ε) (hε : ε ≤ ε') : TVLe μ ν ε' := fun S hS =>
  ⟨(h S hS).1.trans (by gcongr), (h S hS).2.trans (by gcongr)⟩

/-- **Every pair of measures is within distance `⊤`.** The bound is valued in `ℝ≥0∞`, so
there is always a — useless — bound to be had. -/
@[simp] theorem tvLe_top (μ ν : Measure Ω) : TVLe μ ν ⊤ := by
  intro S _
  simp

/-- **The triangle inequality.** Errors add along a chain of approximations: an `ε`-good
sampler for `ν` and a `δ`-good sampler for `ξ` differ by at most `ε + δ`. -/
theorem TVLe.trans (h₁ : TVLe μ ν ε) (h₂ : TVLe ν ξ δ) : TVLe μ ξ (ε + δ) := by
  intro S hS
  obtain ⟨a₁, b₁⟩ := h₁ S hS
  obtain ⟨a₂, b₂⟩ := h₂ S hS
  refine ⟨?_, ?_⟩
  · calc μ S ≤ ν S + ε := a₁
      _ ≤ ξ S + δ + ε := by gcongr
      _ = ξ S + (ε + δ) := by ring
  · calc ξ S ≤ ν S + δ := b₂
      _ ≤ μ S + ε + δ := by gcongr
      _ = μ S + (ε + δ) := by ring

/-- **The pseudometric separates points**: a sampler with zero error is exact. -/
theorem TVLe.eq_of_zero (h : TVLe μ ν 0) : μ = ν := by
  ext S hS
  obtain ⟨a, b⟩ := h S hS
  rw [add_zero] at a b
  exact le_antisymm a b

/-- `TVLe μ ν 0` is exactly equality of measures. -/
theorem tvLe_zero_iff : TVLe μ ν 0 ↔ μ = ν :=
  ⟨TVLe.eq_of_zero, fun h => h ▸ TVLe.refl μ⟩

/-! ## Transferring a bound on an event

The reason the whole notion is worth having: a probability computed for the *target* is
still valid for whatever the sampler actually produced, degraded by exactly the sampler's
error. -/

/-- **Transfer of an upper bound.** If `μ` is within `ε` of `ν` and the event `S` is rare
under `ν`, it is rare under `μ` too, with the probability inflated by `ε`.

This is the lemma a sampler's caller uses: `ν` is the target, `μ` is the law of the
approximate sample, `p` is whatever failure probability the analysis of the target
established. -/
theorem TVLe.measure_le_add (h : TVLe μ ν ε) (hS : MeasurableSet S) (hp : ν S ≤ p) :
    μ S ≤ p + ε :=
  (h S hS).1.trans (by gcongr)

/-- **Transfer of a lower bound.** An event that is likely under `ν` cannot be too unlikely
under `μ`. -/
theorem TVLe.le_measure_add (h : TVLe μ ν ε) (hS : MeasurableSet S) (hp : p ≤ ν S) :
    p ≤ μ S + ε :=
  hp.trans (h S hS).2

/-- Transfer in the other direction, for convenience: a bound established for `μ`
transfers to `ν`. Just `TVLe.measure_le_add` applied to the symmetric statement. -/
theorem TVLe.measure_le_add' (h : TVLe μ ν ε) (hS : MeasurableSet S) (hp : μ S ≤ p) :
    ν S ≤ p + ε :=
  h.symm.measure_le_add hS hp

/-- The complementary event carries the same bound — immediate, since the definition
already quantifies over all measurable sets, but worth recording so that callers holding a
bound on `S` need not rebuild the measurability of `Sᶜ`. -/
theorem TVLe.compl (h : TVLe μ ν ε) (hS : MeasurableSet S) :
    μ Sᶜ ≤ ν Sᶜ + ε ∧ ν Sᶜ ≤ μ Sᶜ + ε :=
  h Sᶜ hS.compl

/-! ## Probability measures -/

/-- **For probability measures one inequality suffices.** Applying the hypothesis to `Sᶜ`
and cancelling the (finite) mass `ν Sᶜ` recovers the reverse bound, so there is no need to
check both directions by hand. -/
theorem tvLe_of_forall_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ S : Set Ω, MeasurableSet S → μ S ≤ ν S + ε) : TVLe μ ν ε := by
  intro S hS
  refine ⟨h S hS, ?_⟩
  have hμ : μ S + μ Sᶜ = 1 := by rw [measure_add_measure_compl hS, measure_univ]
  have hν : ν S + ν Sᶜ = 1 := by rw [measure_add_measure_compl hS, measure_univ]
  have key : ν S + ν Sᶜ ≤ μ S + ε + ν Sᶜ := by
    rw [hν, ← hμ]
    calc μ S + μ Sᶜ ≤ μ S + (ν Sᶜ + ε) := by gcongr; exact h Sᶜ hS.compl
      _ = μ S + ε + ν Sᶜ := by ring
  exact ENNReal.le_of_add_le_add_right (measure_ne_top ν Sᶜ) key

/-- On probability measures the distance is at most `1`. -/
theorem tvLe_one (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    TVLe μ ν 1 := by
  intro S _
  constructor
  · exact le_add_left (prob_le_one)
  · exact le_add_left (prob_le_one)

/-! ## The real-valued form of the bound

`TVLe` is stated in `ℝ≥0∞` so that the pseudometric laws need no finiteness side
conditions. Integrals, however, live in `ℝ`, so the transfer lemma has to be restated
there. On finite measures and for a finite bound this is lossless. -/

/-- **The transfer lemma, real form.** On finite measures a `TVLe` bound with `ε ≠ ⊤`
becomes the real inequality `μ.real S ≤ ν.real S + ε.toReal`. -/
theorem TVLe.measureReal_le_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : TVLe μ ν ε)
    (hε : ε ≠ ⊤) (hS : MeasurableSet S) : μ.real S ≤ ν.real S + ε.toReal := by
  have hne : ν S + ε ≠ ⊤ := ENNReal.add_ne_top.2 ⟨measure_ne_top ν S, hε⟩
  have := ENNReal.toReal_mono hne (h S hS).1
  rwa [ENNReal.toReal_add (measure_ne_top ν S) hε] at this

/-- **Both directions at once**: on finite measures, `|μ.real S − ν.real S| ≤ ε.toReal`.
This is the form the layer-cake argument for `TVLe.integral_le` consumes. -/
theorem TVLe.abs_measureReal_sub_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : TVLe μ ν ε) (hε : ε ≠ ⊤) (hS : MeasurableSet S) :
    |μ.real S - ν.real S| ≤ ε.toReal := by
  have h₁ := h.measureReal_le_add hε hS
  have h₂ := h.symm.measureReal_le_add hε hS
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## The layer-cake tail function

`∫ f ∂μ = ∫_{(0,1]} μ.real {x | t ≤ f x} dt` for `f` with values in `[0,1]`
(`MeasureTheory.Integrable.integral_eq_integral_Ioc_meas_le`). The two lemmas here supply
the regularity of the integrand `t ↦ μ.real {x | t ≤ f x}` that the argument needs. -/

/-- The layer-cake tail function `t ↦ μ.real {x | t ≤ f x}` is measurable, being the
`toReal` of an antitone `ℝ≥0∞`-valued function. No measurability of `f` is needed. -/
theorem measurable_measureReal_tail (μ : Measure Ω) (f : Ω → ℝ) :
    Measurable fun t : ℝ => μ.real {x | t ≤ f x} := by
  refine Measurable.ennreal_toReal (Antitone.measurable fun s t hst => ?_)
  exact measure_mono fun x hx => hst.trans hx

/-- The layer-cake tail function is integrable on `(0,1]`: it is measurable and bounded by
the total mass, on a set of finite Lebesgue measure. -/
theorem integrableOn_measureReal_tail (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) :
    IntegrableOn (fun t : ℝ => μ.real {x | t ≤ f x}) (Ioc (0 : ℝ) 1) volume := by
  have hconst : IntegrableOn (fun _ : ℝ => (μ univ).toReal) (Ioc (0 : ℝ) 1) volume :=
    integrableOn_const (by simp [Real.volume_Ioc])
  refine Integrable.mono' hconst
    ((measurable_measureReal_tail μ f).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_mono (subset_univ _) (measure_ne_top μ univ)

/-! ## The headline: transferring a bound to an expectation

A `TVLe` bound controls not just probabilities of events but expectations of bounded
observables, with the *same* constant and no extra loss. This is the form that
Kannan–Vempala-style volume arguments consume: a payoff `f` with values in `[0,1]`
evaluated against an approximate sample instead of the target. -/

/-- A measurable function with values in `[0,1]` is integrable against a finite measure. -/
theorem integrable_of_forall_mem_Icc {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : Integrable f μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
  exact hf1 x

/-- **The transfer lemma for observables.** If `μ` and `ν` are probability measures within
total variation distance `ε < ⊤`, then for every measurable `f : Ω → ℝ` with
`0 ≤ f x ≤ 1` for all `x`,

  `|∫ f ∂μ − ∫ f ∂ν| ≤ ε.toReal`.

Proof by the layer-cake representation `∫ f = ∫_{(0,1]} μ.real {x | t ≤ f x} dt`
(`MeasureTheory.Integrable.integral_eq_integral_Ioc_meas_le`): the two integrands differ by
at most `ε.toReal` pointwise in `t` by `TVLe.abs_measureReal_sub_le`, and `(0,1]` has
Lebesgue measure `1`, so integrating loses nothing. -/
theorem TVLe.integral_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : TVLe μ ν ε) (hε : ε ≠ ⊤) {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ ε.toReal := by
  have hmS : ∀ t : ℝ, MeasurableSet {x | t ≤ f x} := fun _ =>
    measurableSet_le measurable_const hf
  have hlcμ : ∫ x, f x ∂μ = ∫ t in Ioc (0 : ℝ) 1, μ.real {x | t ≤ f x} :=
    (integrable_of_forall_mem_Icc hf hf0 hf1).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hf1)
  have hlcν : ∫ x, f x ∂ν = ∫ t in Ioc (0 : ℝ) 1, ν.real {x | t ≤ f x} :=
    (integrable_of_forall_mem_Icc hf hf0 hf1).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hf1)
  have hgμ := integrableOn_measureReal_tail μ f
  have hgν := integrableOn_measureReal_tail ν f
  calc |∫ x, f x ∂μ - ∫ x, f x ∂ν|
      = |∫ t in Ioc (0 : ℝ) 1, (μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x})| := by
        rw [hlcμ, hlcν, integral_sub hgμ hgν]
    _ ≤ ∫ t in Ioc (0 : ℝ) 1, |μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x}| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _t in Ioc (0 : ℝ) 1, ε.toReal :=
        integral_mono (hgμ.sub hgν).abs (integrableOn_const (by simp [Real.volume_Ioc]))
          fun t => h.abs_measureReal_sub_le hε (hmS t)
    _ = ε.toReal := by
        rw [setIntegral_const]
        simp

/-! ## Data processing, deterministic case -/

/-- **Post-processing cannot increase the distance.** Pushing both measures forward along a
measurable map `f` — reporting `f x` instead of the sample `x` — preserves the bound. -/
theorem TVLe.map (h : TVLe μ ν ε) {f : Ω → Ω'} (hf : Measurable f) :
    TVLe (μ.map f) (ν.map f) ε := by
  intro S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hf hS]
  exact h _ (hf hS)

/-! ## Warmness

A *warm start* is the other standard way of saying that one distribution approximates
another: `μ` is `M`-warm with respect to `ν` when `μ S ≤ M * ν S` for every measurable `S`,
i.e. `sup_S μ S / ν S ≤ M`. Unlike `TVLe` this is a multiplicative, one-sided comparison,
so it composes by multiplication rather than by addition. -/

/-- **`M`-warmness**: `μ S ≤ M * ν S` for every measurable `S`, i.e. `sup_S μ S / ν S ≤ M`.
This is the warm-start parameter of the volume-computation literature. -/
def IsWarm (M : ℝ≥0∞) (μ ν : Measure Ω) : Prop :=
  ∀ S : Set Ω, MeasurableSet S → μ S ≤ M * ν S

/-- Unfolding lemma for `IsWarm`. -/
theorem isWarm_iff (M : ℝ≥0∞) (μ ν : Measure Ω) :
    IsWarm M μ ν ↔ ∀ S : Set Ω, MeasurableSet S → μ S ≤ M * ν S := Iff.rfl

/-- **Every measure is `1`-warm with respect to itself.** -/
@[simp] theorem IsWarm.refl (μ : Measure Ω) : IsWarm 1 μ μ := by
  intro S _
  simp

/-- **Warmness constants multiply along a chain.** -/
theorem IsWarm.trans {M M' : ℝ≥0∞} (h₁ : IsWarm M μ ν) (h₂ : IsWarm M' ν ξ) :
    IsWarm (M * M') μ ξ := by
  intro S hS
  calc μ S ≤ M * ν S := h₁ S hS
    _ ≤ M * (M' * ξ S) := by gcongr; exact h₂ S hS
    _ = M * M' * ξ S := (mul_assoc _ _ _).symm

/-- **A warmness constant may always be weakened.** -/
theorem IsWarm.mono {M M' : ℝ≥0∞} (h : IsWarm M μ ν) (hM : M ≤ M') : IsWarm M' μ ν :=
  fun S hS => (h S hS).trans (by gcongr)

/-- Between probability measures the warmness constant is at least `1`: take `S = univ`. -/
theorem IsWarm.one_le {M : ℝ≥0∞} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : IsWarm M μ ν) : 1 ≤ M := by
  have := h univ MeasurableSet.univ
  simpa using this

/-- **Warmness controls total variation.** For probability measures, `M`-warmness with
`1 ≤ M` gives `TVLe μ ν (M - 1)`: the excess mass an `M`-warm measure can put on any event
is at most `M - 1`, since the event has `ν`-mass at most `1`.

The reverse implication is false — `TVLe` allows `ν S = 0 < μ S` — so warmness is the
strictly stronger notion. -/
theorem IsWarm.tvLe {M : ℝ≥0∞} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : IsWarm M μ ν) (hM : 1 ≤ M) : TVLe μ ν (M - 1) := by
  refine tvLe_of_forall_le fun S hS => ?_
  calc μ S ≤ M * ν S := h S hS
    _ = (M - 1 + 1) * ν S := by rw [tsub_add_cancel_of_le hM]
    _ = (M - 1) * ν S + ν S := by rw [add_mul, one_mul]
    _ ≤ (M - 1) * 1 + ν S := by gcongr; exact prob_le_one
    _ = ν S + (M - 1) := by rw [mul_one, add_comm]

end Arlib
