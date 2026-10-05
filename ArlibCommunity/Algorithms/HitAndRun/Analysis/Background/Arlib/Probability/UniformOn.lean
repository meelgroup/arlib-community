/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.Rejection
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.TV
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The uniform measure on a set of positive finite measure

`Arlib.uniformOn μ S` is the measure `μ` restricted to `S` and renormalised to total
mass `1`.  When `μ` is Lebesgue measure and `S` is a convex body, this is *the uniform
distribution on the body* — the reference distribution a volume/sampling algorithm is
measured against ("a density whose variational distance to the uniform density on `P'`
is at most `ε`", Kannan–Vempala Theorem 2).

## The definition is `Arlib.condOn`

The object `(μ S)⁻¹ • μ.restrict S` already exists in this library, as
`Arlib.condOn` (`Arlib/Probability/Rejection.lean`), under its *conditioning* reading:
the law of a `μ`-draw conditioned on landing in `S`.  Those two readings — "condition a
draw on `S`" and "sample uniformly from `S`" — are the *same measure*, so `uniformOn` is
a plain abbreviation for `condOn` rather than a second copy of it, and every `condOn`
lemma applies verbatim.  The names are kept apart only because a caller writing a volume
algorithm wants to read `uniformOn volume P`, not `condOn volume P`.

What this file adds on top of `Rejection.lean` is the **integral API**, which is what a
total-variation statement about a sampler actually consumes.

## Main results

* `Arlib.uniformOn` — the definition (an abbreviation for `Arlib.condOn`), plus the
  event API `uniformOn_apply`, `isProbabilityMeasure_uniformOn`,
  `uniformOn_compl_eq_zero`, `uniformOn_self`.
* `Arlib.integral_uniformOn` — **the headline**:
  `∫ x, f x ∂(uniformOn μ S) = (μ S).toReal⁻¹ * ∫ x in S, f x ∂μ`.
* `Arlib.setIntegral_eq_measure_mul_integral_uniformOn` — the same identity solved the
  other way, `∫ x in S, f x ∂μ = (μ S).toReal * ∫ x, f x ∂(uniformOn μ S)`.  *This* is
  the direction that genuinely needs `μ S ≠ 0` and `μ S ≠ ⊤`.
* `Arlib.integral_uniformOn_nonneg`, `Arlib.integral_uniformOn_le_one` — the `0 ≤ f ≤ 1`
  bounds, the shape `Arlib.TVLe.integral_le` consumes.
* `Arlib.uniformOn_absolutelyContinuous`, `Arlib.uniformOn_eq_withDensity` — the density
  `(μ S)⁻¹ • S.indicator 1` with respect to `μ`.
* `Arlib.uniformOn_unitInterval_*` — the **non-vacuity witnesses**: `Set.Icc (0:ℝ) 1`
  has `volume` equal to `1`, so it satisfies `0 < μ S < ⊤`, and `uniformOn` on it is
  computed explicitly.

## The `x / 0 = 0` hazard

With Mathlib's conventions `(0 : ℝ≥0∞)⁻¹ = ⊤`, `(⊤ : ℝ≥0∞)⁻¹ = 0` and `x / 0 = 0`, the
*definition* `uniformOn μ S` is perfectly well typed when `μ S` is `0` or `⊤` — it is
just not a probability measure there, and a lemma that forgets to say so can be silently
vacuous.  Every statement below that asserts anything about total mass carries the
guards `μ S ≠ 0` and `μ S ≠ ⊤` explicitly.

Two statements are *unconditional*, and deliberately so: `uniformOn_apply` (both sides
degenerate the same way) and `integral_uniformOn` (because `ENNReal.toReal_inv` is
unconditional, `(μ S)⁻¹.toReal = (μ S).toReal⁻¹` even at `0` and `⊤`, and both sides are
then `0`).  Stating those with unused hypotheses would only weaken them; the guarded
consequences that a caller needs are `isProbabilityMeasure_uniformOn` and
`setIntegral_eq_measure_mul_integral_uniformOn`, which do carry them.
-/

namespace Arlib

open MeasureTheory
open scoped ENNReal

section UniformOn

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The uniform measure on `S`**: `μ` restricted to `S`, renormalised by `μ S`.

This is definitionally `Arlib.condOn μ S`; the two names record two readings of one
measure.  `condOn μ S` is "the law of a `μ`-draw conditioned on landing in `S`";
`uniformOn μ S` is "the uniform distribution on `S`", which is what that conditioned law
*is* when `μ` is the ambient volume.  Consumers of a volume algorithm want the second
reading, so the abbreviation exists; but it is the same object, and every lemma about
`condOn` applies to it unchanged.

It is a probability measure exactly when `μ S ∉ {0, ∞}` — see
`isProbabilityMeasure_uniformOn`.  Outside that range Mathlib's `(0)⁻¹ = ⊤` and
`(⊤)⁻¹ = 0` conventions make it the zero measure or an infinite one; the guards are
carried explicitly by the lemmas that need them. -/
noncomputable abbrev uniformOn (μ : Measure Ω) (S : Set Ω) : Measure Ω := condOn μ S

/-- Unfolding lemma for `uniformOn`: it is the renormalised restriction. -/
theorem uniformOn_def (μ : Measure Ω) (S : Set Ω) :
    uniformOn μ S = (μ S)⁻¹ • μ.restrict S := rfl

/-- `uniformOn` and `condOn` are the same measure.  Stated as a lemma so that a proof
which mixes the two readings can `rw` between them instead of relying on
definitional unfolding. -/
theorem uniformOn_eq_condOn (μ : Measure Ω) (S : Set Ω) :
    uniformOn μ S = condOn μ S := rfl

/-! ### Event probabilities -/

/-- **The uniform probability of an event.**  `uniformOn μ S` gives the event `T` the
mass `μ (T ∩ S) / μ S` — "what fraction of `S` lies in `T`".

No guard is needed: if `μ S = 0` then `μ (T ∩ S) = 0` and both sides are `0`, and if
`μ S = ⊤` then `(⊤)⁻¹ = 0` kills the left side while `x / ⊤ = 0` kills the right.  Total
mass is the statement that does need the guards, and it is
`isProbabilityMeasure_uniformOn`. -/
theorem uniformOn_apply (μ : Measure Ω) {S T : Set Ω} (hS : MeasurableSet S)
    (hT : MeasurableSet T) : uniformOn μ S T = μ (T ∩ S) / μ S :=
  condOn_apply μ hS hT

/-- **`uniformOn μ S` is a probability measure** exactly when `S` has positive finite
measure.  Both guards are essential: at `μ S = 0` the measure is `⊤ • 0 = 0`, and at
`μ S = ⊤` it is `0 • _ = 0`; in either case the total mass is `0`, not `1`. -/
theorem isProbabilityMeasure_uniformOn (μ : Measure Ω) {S : Set Ω} (h0 : μ S ≠ 0)
    (htop : μ S ≠ ⊤) : IsProbabilityMeasure (uniformOn μ S) :=
  isProbabilityMeasure_condOn μ h0 htop

/-- The total mass of `uniformOn μ S` is `1` when `0 < μ S < ⊤`. -/
theorem uniformOn_univ (μ : Measure Ω) {S : Set Ω} (h0 : μ S ≠ 0) (htop : μ S ≠ ⊤) :
    uniformOn μ S Set.univ = 1 :=
  condOn_univ μ h0 htop

/-- **`uniformOn μ S` lives on `S`**: nothing outside `S` gets any mass. -/
theorem uniformOn_compl_eq_zero (μ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S) :
    uniformOn μ S Sᶜ = 0 :=
  condOn_compl_eq_zero μ hS

/-- **All of the mass is on `S`.**  Together with `uniformOn_compl_eq_zero` this says the
uniform measure is supported exactly on `S`.  The guards are needed: without them the
measure is `0` and this reads `0 = 1`. -/
theorem uniformOn_self (μ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S) (h0 : μ S ≠ 0)
    (htop : μ S ≠ ⊤) : uniformOn μ S S = 1 := by
  rw [uniformOn_apply μ hS hS, Set.inter_self, ENNReal.div_self h0 htop]

end UniformOn

/-! ### The integral formula

This is what the file exists for.  A total-variation hypothesis "the sampler's law `ρ` is
within `ε` of uniform on `P`" is converted by `Arlib.TVLe.integral_le` into a statement
about `∫ f ∂(uniformOn volume P)`; the lemmas here turn that into the *average of `f` over
`P`*, `(Vol P)⁻¹ ∫_P f`, which is the form the theorem is stated in on paper. -/

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **The headline: the integral against the uniform measure is the average over `S`.**

    ∫ x, f x ∂(uniformOn μ S) = (μ S).toReal⁻¹ • ∫ x in S, f x ∂μ

`uniformOn μ S` is the scalar `(μ S)⁻¹` times `μ.restrict S`, so this is
`MeasureTheory.integral_smul_measure` followed by `ENNReal.toReal_inv` to move the
inverse from `ℝ≥0∞` to `ℝ`.  Note the direction: the scalar that comes out of
`integral_smul_measure` is `(μ S)⁻¹.toReal`, and it is `ENNReal.toReal_inv` — which is
unconditional — that rewrites it to `(μ S).toReal⁻¹`.

**No integrability hypothesis, and no `μ S ≠ 0` / `μ S ≠ ⊤` guards are needed**, and
adding them would only weaken the lemma.  `integral_smul_measure` holds for every scalar
including `⊤` (where Bochner integration against an infinite measure returns `0`), and at
`μ S = 0` both sides are `0` because `(0 : ℝ)⁻¹ = 0`.  The statement is still only
*informative* in the range `0 < μ S < ⊤`; the guarded companion that a caller multiplying
through by the volume needs is
`setIntegral_eq_measure_mul_integral_uniformOn`, and non-vacuity of that range is
witnessed by `uniformOn_unitInterval_integral` below. -/
theorem integral_uniformOn (μ : Measure Ω) (S : Set Ω) (f : Ω → E) :
    ∫ x, f x ∂(uniformOn μ S) = (μ S).toReal⁻¹ • ∫ x in S, f x ∂μ := by
  rw [uniformOn_def, integral_smul_measure, ENNReal.toReal_inv]

/-- **The headline for real-valued `f`**, with the scalar action written as
multiplication:

    ∫ x, f x ∂(uniformOn μ S) = (μ S).toReal⁻¹ * ∫ x in S, f x ∂μ.

This is `integral_uniformOn` with `E = ℝ`; it is stated separately because `•` on `ℝ`
does not reduce to `*` by `rfl` in every elaboration context, and this is the form the
Kannan–Vempala display uses. -/
theorem integral_uniformOn_real (μ : Measure Ω) (S : Set Ω) (f : Ω → ℝ) :
    ∫ x, f x ∂(uniformOn μ S) = (μ S).toReal⁻¹ * ∫ x in S, f x ∂μ := by
  rw [integral_uniformOn, smul_eq_mul]

/-- **The headline, solved for the set integral.**  This is the direction in which the
guards are load-bearing: cancelling `(μ S).toReal * (μ S).toReal⁻¹` to `1` requires
`(μ S).toReal ≠ 0`, i.e. exactly `μ S ≠ 0` *and* `μ S ≠ ⊤` (`ENNReal.toReal` sends both
degenerate values to the real number `0`).

    ∫ x in S, f x ∂μ = (μ S).toReal • ∫ x, f x ∂(uniformOn μ S).

Read right to left: the mass of `f` over `S` is the volume of `S` times the `f`-average of
a uniform sample from `S`. -/
theorem setIntegral_eq_measure_mul_integral_uniformOn (μ : Measure Ω) {S : Set Ω}
    (h0 : μ S ≠ 0) (htop : μ S ≠ ⊤) (f : Ω → E) :
    ∫ x in S, f x ∂μ = (μ S).toReal • ∫ x, f x ∂(uniformOn μ S) := by
  have hne : (μ S).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩
  rw [integral_uniformOn, smul_smul, mul_inv_cancel₀ hne, one_smul]

end Integral

/-! ### Bounds for `[0,1]`-valued observables

`Arlib.TVLe.integral_le` transfers a total-variation bound to observables `f` with
`0 ≤ f ≤ 1`.  These two lemmas say that the `uniformOn` side of such a transfer is itself
a number in `[0,1]`, so the conclusion can be chained without leaving that range. -/

section Bounds

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A nonnegative observable has nonnegative uniform average.**  No guards: at
`μ S ∈ {0, ⊤}` the integral is `0`, which is still `≥ 0`. -/
theorem integral_uniformOn_nonneg (μ : Measure Ω) (S : Set Ω) {f : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) : 0 ≤ ∫ x, f x ∂(uniformOn μ S) :=
  integral_nonneg hf0

/-- **An observable bounded by `1` has uniform average at most `1`.**

The guards `μ S ≠ 0`, `μ S ≠ ⊤` are essential *as stated with `f` only bounded above*:
they are what makes `uniformOn μ S` a probability measure, so that `∫ 1 = 1`.  (Without
them the conclusion happens to survive because the integral collapses to `0`, but that is
an accident of the degenerate case and not what a caller means.)

Integrability is not a hypothesis: a measurable `[0,1]`-valued function is automatically
integrable against a finite measure, by `Arlib.integrable_of_forall_mem_Icc`. -/
theorem integral_uniformOn_le_one (μ : Measure Ω) {S : Set Ω} (h0 : μ S ≠ 0)
    (htop : μ S ≠ ⊤) {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) : ∫ x, f x ∂(uniformOn μ S) ≤ 1 := by
  haveI : IsProbabilityMeasure (uniformOn μ S) := isProbabilityMeasure_uniformOn μ h0 htop
  calc ∫ x, f x ∂(uniformOn μ S)
      ≤ ∫ _x, (1 : ℝ) ∂(uniformOn μ S) :=
        integral_mono (integrable_of_forall_mem_Icc hf hf0 hf1) (integrable_const 1) hf1
    _ = 1 := by simp

/-- **The uniform average of a `[0,1]`-valued observable lies in `[0,1]`.**  The two
previous lemmas packaged together, which is the shape a `TVLe` chain wants. -/
theorem integral_uniformOn_mem_Icc (μ : Measure Ω) {S : Set Ω} (h0 : μ S ≠ 0)
    (htop : μ S ≠ ⊤) {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) : ∫ x, f x ∂(uniformOn μ S) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨integral_uniformOn_nonneg μ S hf0, integral_uniformOn_le_one μ h0 htop hf hf0 hf1⟩

end Bounds

/-! ### Absolute continuity and the density -/

section Density

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`uniformOn μ S` is absolutely continuous with respect to `μ`.**  A `μ`-null set is
null for the restriction, and scaling by an `ℝ≥0∞` constant preserves that.  No guards:
this holds for every value of `μ S`, degenerate ones included. -/
theorem uniformOn_absolutelyContinuous (μ : Measure Ω) (S : Set Ω) :
    uniformOn μ S ≪ μ :=
  (Measure.smul_absolutelyContinuous).trans (Measure.restrict_le_self.absolutelyContinuous)

/-- **The uniform density.**  `uniformOn μ S` is `μ` with density `(μ S)⁻¹ • 𝟙_S`:

    uniformOn μ S = μ.withDensity ((μ S)⁻¹ • S.indicator 1).

Unconditional — the two degenerate values of `μ S` produce the same measure on both
sides.  This identifies the "uniform density on `S`" of the paper's phrasing with the
measure defined here. -/
theorem uniformOn_eq_withDensity (μ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S) :
    uniformOn μ S = μ.withDensity ((μ S)⁻¹ • S.indicator (1 : Ω → ℝ≥0∞)) := by
  rw [withDensity_smul _ ((measurable_one : Measurable (1 : Ω → ℝ≥0∞)).indicator hS),
    withDensity_indicator_one hS, uniformOn_def]

end Density

/-! ### Non-vacuity witness: the unit interval

Every guarded lemma above assumes `μ S ≠ 0` and `μ S ≠ ⊤`.  If no set satisfied both,
all of them would be vacuously true and this file would be worthless (`CLAUDE.md` §11).
The unit interval `Set.Icc (0:ℝ) 1` under Lebesgue measure is such a set — its measure is
exactly `1` — and the section below computes `uniformOn` on it explicitly, event
probabilities and integral alike. -/

section UnitInterval

open scoped Real

/-- The unit interval has Lebesgue measure `1`: it is neither null nor infinite, so it
discharges both guards. -/
theorem volume_unitInterval : volume (Set.Icc (0 : ℝ) 1) = 1 := by
  rw [Real.volume_Icc]
  norm_num

/-- The first guard, discharged: `Set.Icc (0:ℝ) 1` is not null. -/
theorem volume_unitInterval_ne_zero : volume (Set.Icc (0 : ℝ) 1) ≠ 0 := by
  rw [volume_unitInterval]; exact one_ne_zero

/-- The second guard, discharged: `Set.Icc (0:ℝ) 1` has finite measure. -/
theorem volume_unitInterval_ne_top : volume (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
  rw [volume_unitInterval]; exact ENNReal.one_ne_top

/-- **The witness is a genuine probability measure.**  This is the fact that makes
`isProbabilityMeasure_uniformOn` non-vacuous. -/
theorem isProbabilityMeasure_uniformOn_unitInterval :
    IsProbabilityMeasure (uniformOn volume (Set.Icc (0 : ℝ) 1)) :=
  isProbabilityMeasure_uniformOn volume volume_unitInterval_ne_zero volume_unitInterval_ne_top

/-- Because the normalising constant is `1`, the uniform measure on the unit interval is
just Lebesgue measure restricted to it. -/
theorem uniformOn_unitInterval_eq_restrict :
    uniformOn volume (Set.Icc (0 : ℝ) 1) = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  rw [uniformOn_def, volume_unitInterval, inv_one, one_smul]

/-- **A concrete event probability.**  A uniform draw from `[0,1]` lands in `(-∞, 1/2]`
with probability exactly `1/2`.  This is the file's smallest end-to-end check that
`uniformOn` computes the intended numbers. -/
theorem uniformOn_unitInterval_Iic_half :
    uniformOn volume (Set.Icc (0 : ℝ) 1) (Set.Iic (1 / 2)) = 1 / 2 := by
  have hinter : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [uniformOn_apply volume measurableSet_Icc measurableSet_Iic, hinter,
    volume_unitInterval, div_one, Real.volume_Icc]
  rw [show (1 / 2 : ℝ) - 0 = 1 / 2 by ring, ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- **The headline, instantiated on the witness.**  For every `f`, the uniform average
over `[0,1]` is the plain set integral, because the normalising constant is `1`.  This
exhibits `integral_uniformOn` at a set with `0 < μ S < ⊤`, so the headline is not
vacuously about degenerate sets. -/
theorem uniformOn_unitInterval_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ x, f x ∂(uniformOn volume (Set.Icc (0 : ℝ) 1)) = ∫ x in Set.Icc (0 : ℝ) 1, f x := by
  rw [integral_uniformOn, volume_unitInterval, ENNReal.toReal_one, inv_one, one_smul]

end UnitInterval

/-! ### Non-vacuity witness: a metric ball

The unit interval above is the cheapest witness; this is the one a convex-body sampler
actually meets.  In any proper metric space carrying a measure that is positive on
nonempty opens and finite on compacts — Lebesgue measure on `EuclideanSpace ℝ (Fin n)`
being the case of interest — every ball of positive radius has `0 < μ B < ⊤`, so
`uniformOn μ B` is the uniform distribution on that ball. -/

section Ball

variable {Ω : Type*} [PseudoMetricSpace Ω] [ProperSpace Ω] [MeasurableSpace Ω]
  (μ : Measure Ω) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]

omit [ProperSpace Ω] [IsFiniteMeasureOnCompacts μ] in
/-- The first guard for a ball: positive radius gives positive measure, because a ball is
a nonempty open set. -/
theorem measure_ball_ne_zero' (x : Ω) {r : ℝ} (hr : 0 < r) : μ (Metric.ball x r) ≠ 0 :=
  (Metric.measure_ball_pos μ x hr).ne'

omit [Measure.IsOpenPosMeasure μ] in
/-- The second guard for a ball: in a proper space a ball is bounded, hence of finite
measure. -/
theorem measure_ball_ne_top' (x : Ω) (r : ℝ) : μ (Metric.ball x r) ≠ ⊤ :=
  measure_ball_ne_top

/-- **The uniform distribution on a ball is a probability measure.**  Instantiated at
`μ = volume` on `EuclideanSpace ℝ (Fin n)` this is the reference distribution of a
convex-body sampler, and it shows the guards of every lemma in this file are satisfiable
in the setting they were written for. -/
theorem isProbabilityMeasure_uniformOn_ball (x : Ω) {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (uniformOn μ (Metric.ball x r)) :=
  isProbabilityMeasure_uniformOn μ (measure_ball_ne_zero' μ x hr) (measure_ball_ne_top' μ x r)

omit [ProperSpace Ω] [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ] in
/-- **The headline on a ball.**  The average of `f` over a ball is its integral over the
ball divided by the ball's volume.  The scalar is genuinely nonzero and finite here —
`measure_ball_ne_zero'` and `measure_ball_ne_top'` — so unlike the fully general
`integral_uniformOn` this instance is guaranteed to be about a real average. -/
theorem integral_uniformOn_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Ω) (r : ℝ) (f : Ω → E) :
    ∫ y, f y ∂(uniformOn μ (Metric.ball x r)) =
      (μ (Metric.ball x r)).toReal⁻¹ • ∫ y in Metric.ball x r, f y ∂μ :=
  integral_uniformOn μ (Metric.ball x r) f

/-- The mass of `f` over a ball, recovered from the uniform average by multiplying by the
ball's volume.  Requires positive radius, since that is what makes the volume nonzero. -/
theorem setIntegral_ball_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Ω) {r : ℝ} (hr : 0 < r) (f : Ω → E) :
    ∫ y in Metric.ball x r, f y ∂μ =
      (μ (Metric.ball x r)).toReal • ∫ y, f y ∂(uniformOn μ (Metric.ball x r)) :=
  setIntegral_eq_measure_mul_integral_uniformOn μ (measure_ball_ne_zero' μ x hr)
    (measure_ball_ne_top' μ x r) f

end Ball

end Arlib
