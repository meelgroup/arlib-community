/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Conductance of a Markov kernel on a general measurable space

Mathlib has Markov kernels (`ProbabilityTheory.Kernel`), invariance
(`ProbabilityTheory.Kernel.Invariant`) and irreducibility, but no notion of
*conductance* and no quantitative convergence rate.  This module supplies the
definitional layer: the ergodic flow, reversibility, and the conductance of a
kernel with respect to an invariant measure, on an arbitrary measurable space.
It is the continuous-state counterpart of
`Arlib.MarkovChains.Techniques.Conductance` (which is finite-state and real
valued); everything here is `ℝ≥0∞` valued, so no integrability side conditions
are ever needed.

## Main definitions

* `Arlib.MarkovChains.flow P pi S T = ∫⁻ x in S, P x T ∂pi` — the **ergodic
  flow** from `S` to `T`: the `pi`-probability that one step of the chain starts
  in `S` and lands in `T`.
* `Arlib.MarkovChains.IsReversible P pi` — **detailed balance**, stated as
  symmetry of the flow on measurable rectangles.
* `Arlib.MarkovChains.conductanceOn P pi S = flow P pi S Sᶜ / pi S` — the
  conductance of a single set: the conditional probability of escaping `S` in
  one step.
* `Arlib.MarkovChains.conductanceWithin P pi thr` — the infimum of
  `conductanceOn` over the measurable sets `S` with `0 < pi S ≤ thr`, and
  `Arlib.MarkovChains.conductance P pi = conductanceWithin P pi (1/2)`, the
  conductance proper.

## Main results

* `flow_univ_right`, `flow_le`, `flow_iUnion`, `flow_mono_left`,
  `flow_mono_right` — the flow calculus.
* `IsReversible.invariant` — **detailed balance implies stationarity**.
* `conductanceOn_le_one`, `conductanceOn_lt_top` — `conductanceOn` really is a
  number in `[0,1]` once `0 < pi S < ∞`; it is neither trivially `0` nor `⊤`.
* `conductanceOn_smul`, `conductanceWithin_smul` — invariance under rescaling
  the measure.
* `conductance_const_piHalf` — the **non-vacuity witness** (`CLAUDE.md` §11):
  a concrete kernel and measure whose conductance is provably `1/2`.

## Degenerate values: a warning

`ℝ≥0∞` has `x / 0 = 0`, so `conductanceOn P pi S` is `0` — not `⊤`, not
"undefined" — as soon as `pi S = 0`.  *Every* statement below whose content is
about the size of a conductance therefore carries an explicit `0 < pi S`
hypothesis; without it the statement would be true but empty.  For the same
reason the infimum defining `conductance` ranges only over sets of positive
measure, and `conductance_le_one` needs the family of such sets to be
non-empty (an infimum over the empty family is `⊤`); see
`conductance_eq_top_of_isEmpty` for the converse.

## Design note: the `1/2` threshold and rescaling

`conductance` cuts the infimum off at `pi S ≤ 1/2`, as is standard for a
*probability* measure `pi`.  That threshold is an absolute constant, so
`conductance P (c • pi) = conductance P pi` is **false** in general: rescaling
`pi` by `c` changes which sets are admissible.  What is true, and is proved
here, is that the individual quotients are scale invariant
(`conductanceOn_smul`) and that the infimum is scale invariant once the
threshold is rescaled along with the measure (`conductanceWithin_smul`).

## References

The definition is the one used by Lovász–Simonovits and, in the form needed for
the ball walk, by Cousins–Vempala, *Gaussian cooling and `O*(n³)` algorithms for
volume and Gaussian volume*, §4.1.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The ergodic flow -/

/-- The **ergodic flow** from `S` to `T`: `∫_S P_x(T) dpi(x)`, the probability
that a single step of the chain started from `pi` begins in `S` and ends in `T`.

This is the continuous-state analogue of the finite-state
`∑_{x ∈ S} ∑_{y ∈ T} pi x * P x y`. -/
noncomputable def flow (P : Kernel Ω Ω) (pi : Measure Ω) (S T : Set Ω) : ℝ≥0∞ :=
  ∫⁻ x in S, P x T ∂pi

/-- Unfolding lemma for `flow`. -/
theorem flow_apply (P : Kernel Ω Ω) (pi : Measure Ω) (S T : Set Ω) :
    flow P pi S T = ∫⁻ x in S, P x T ∂pi := rfl

/-- Nothing flows out of the empty set. -/
@[simp] theorem flow_empty_left (P : Kernel Ω Ω) (pi : Measure Ω) (T : Set Ω) :
    flow P pi ∅ T = 0 := by
  simp [flow]

/-- Nothing flows into the empty set. -/
@[simp] theorem flow_empty_right (P : Kernel Ω Ω) (pi : Measure Ω) (S : Set Ω) :
    flow P pi S ∅ = 0 := by
  simp [flow]

/-- The flow is monotone in its source set. -/
theorem flow_mono_left (P : Kernel Ω Ω) (pi : Measure Ω) {S S' : Set Ω} (h : S ⊆ S')
    (T : Set Ω) : flow P pi S T ≤ flow P pi S' T :=
  lintegral_mono' (Measure.restrict_mono h le_rfl) le_rfl

/-- The flow is monotone in its target set. -/
theorem flow_mono_right (P : Kernel Ω Ω) (pi : Measure Ω) (S : Set Ω) {T T' : Set Ω}
    (h : T ⊆ T') : flow P pi S T ≤ flow P pi S T' :=
  lintegral_mono fun _ => measure_mono h

/-- The flow is monotone in both arguments. -/
theorem flow_mono (P : Kernel Ω Ω) (pi : Measure Ω) {S S' T T' : Set Ω} (hS : S ⊆ S')
    (hT : T ⊆ T') : flow P pi S T ≤ flow P pi S' T' :=
  (flow_mono_left P pi hS T).trans (flow_mono_right P pi S' hT)

/-- **Everything flows somewhere**: `flow P pi S univ = pi S`.  This is exactly
the statement that `P` is a Markov kernel, and it needs no hypothesis on `pi`. -/
theorem flow_univ_right (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω) (S : Set Ω) :
    flow P pi S Set.univ = pi S := by
  have h : ∀ x : Ω, P x Set.univ = 1 := fun x => measure_univ
  simp only [flow, h]
  rw [setLIntegral_const, one_mul]

/-- The flow out of `S` never exceeds the mass of `S`. -/
theorem flow_le (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω) (S T : Set Ω) :
    flow P pi S T ≤ pi S :=
  (flow_mono_right P pi S (Set.subset_univ T)).trans_eq (flow_univ_right P pi S)

/-- **Countable additivity of the flow in its source set.**  For a countable
family of pairwise disjoint measurable sets, the flow out of the union is the
sum of the flows. -/
theorem flow_iUnion (P : Kernel Ω Ω) (pi : Measure Ω) {ι : Type*} [Countable ι]
    {S : ι → Set Ω} (hm : ∀ i, MeasurableSet (S i)) (hd : Pairwise (Function.onFun Disjoint S))
    (T : Set Ω) : flow P pi (⋃ i, S i) T = ∑' i, flow P pi (S i) T :=
  lintegral_iUnion hm hd _

/-- The flow out of `S` splits over a measurable target and its complement. -/
theorem flow_add_flow_compl_right (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    (S : Set Ω) {T : Set Ω} (hT : MeasurableSet T) :
    flow P pi S T + flow P pi S Tᶜ = pi S := by
  rw [flow, flow, ← lintegral_add_left (Kernel.measurable_coe P hT) _,
    ← flow_univ_right P pi S, flow]
  exact lintegral_congr fun _ => measure_add_measure_compl hT

/-! ## Reversibility

Detailed balance, phrased as symmetry of the flow on measurable rectangles.
Mathlib v4.32 already has this predicate as
`ProbabilityTheory.Kernel.IsReversible`, spelled with the integrals written out;
`isReversible_iff_kernel` identifies the two, and the results below are stated
in terms of `flow` so that the flow calculus applies to them directly. -/

/-- **Detailed balance.** `P` is reversible with respect to `pi` when the flow
across every measurable rectangle is symmetric:
`∫_S P_x(T) dpi(x) = ∫_T P_x(S) dpi(x)`. -/
def IsReversible (P : Kernel Ω Ω) (pi : Measure Ω) : Prop :=
  ∀ S T : Set Ω, MeasurableSet S → MeasurableSet T → flow P pi S T = flow P pi T S

/-- This file's `IsReversible` is Mathlib's `ProbabilityTheory.Kernel.IsReversible`,
written with `flow`. -/
theorem isReversible_iff_kernel (P : Kernel Ω Ω) (pi : Measure Ω) :
    IsReversible P pi ↔ ProbabilityTheory.Kernel.IsReversible P pi :=
  ⟨fun h _ _ hS hT => h _ _ hS hT, fun h _ _ hS hT => h hS hT⟩

/-- **Detailed balance implies stationarity**, in integral form: for a reversible
Markov kernel, `∫ P_x(T) dpi(x) = pi(T)` on every measurable `T`.

The proof is one line of flow calculus: `∫ P_x(T) dpi(x)` is the flow from the
whole space into `T`, reversibility turns it into the flow out of `T` into the
whole space, and that is `pi(T)` because `P` is Markov. -/
theorem IsReversible.lintegral_kernel_apply {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} (h : IsReversible P pi) {T : Set Ω} (hT : MeasurableSet T) :
    ∫⁻ x, P x T ∂pi = pi T := by
  calc ∫⁻ x, P x T ∂pi = flow P pi Set.univ T := by rw [flow, Measure.restrict_univ]
    _ = flow P pi T Set.univ := h _ _ MeasurableSet.univ hT
    _ = pi T := flow_univ_right P pi T

/-- **Detailed balance implies stationarity**: a reversible Markov kernel leaves
`pi` invariant, i.e. `pi.bind P = pi`. -/
theorem IsReversible.invariant {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    (h : IsReversible P pi) : Kernel.Invariant P pi :=
  ((isReversible_iff_kernel P pi).1 h).invariant

/-- **The instantly mixing kernel is reversible.**  For `P x = pi` at every `x`
the flow across a rectangle is the product `pi(T) * pi(S)`, which is symmetric.
This makes `IsReversible` non-vacuous. -/
theorem isReversible_const (pi : Measure Ω) : IsReversible (Kernel.const Ω pi) pi := by
  intro S T _ _
  simp [flow, Kernel.const_apply, mul_comm]

/-! ## Conductance -/

/-- The conductance **of a single set** `S`: the conditional probability that a
step of the chain started from `pi` conditioned on `S` escapes `S`,
`Φ(S) = flow(S, Sᶜ) / pi(S)`.

Because `ℝ≥0∞` divides by zero to zero, this is `0` whenever `pi S = 0`; the
lemmas below therefore all assume `0 < pi S`. -/
noncomputable def conductanceOn (P : Kernel Ω Ω) (pi : Measure Ω) (S : Set Ω) : ℝ≥0∞ :=
  flow P pi S Sᶜ / pi S

/-- Unfolding lemma for `conductanceOn`. -/
theorem conductanceOn_apply (P : Kernel Ω Ω) (pi : Measure Ω) (S : Set Ω) :
    conductanceOn P pi S = flow P pi S Sᶜ / pi S := rfl

/-- **A conductance is a probability, hence at most `1`.**  The numerator
`flow P pi S Sᶜ` is bounded by the denominator `pi S` (`flow_le`), so the
quotient is at most `1`.  (At `pi S = 0` both sides are `0 ≤ 1`, by the
`x / 0 = 0` convention; the statement has content exactly when `0 < pi S`, and
`flow_eq_conductanceOn_mul` is the form that says so.) -/
theorem conductanceOn_le_one (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    (S : Set Ω) : conductanceOn P pi S ≤ 1 :=
  ENNReal.div_le_of_le_mul (by simpa using flow_le P pi S Sᶜ)

/-- **A conductance is finite** as soon as `S` has positive finite measure: the
quotient defining it is a genuine element of `[0,1]`, not `⊤`. -/
theorem conductanceOn_lt_top (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    {S : Set Ω} (hpos : 0 < pi S) (hfin : pi S ≠ ⊤) : conductanceOn P pi S < ⊤ :=
  ENNReal.div_lt_top ((flow_le P pi S Sᶜ).trans_lt hfin.lt_top).ne hpos.ne'

/-- **No information is lost to the division convention**: for `0 < pi S < ∞`
the conductance really does recover the escape flow,
`Φ(S) · pi(S) = flow(S, Sᶜ)`.  Together with `conductanceOn_le_one` this is the
precise sense in which `Φ(S) ∈ [0,1]` is meaningful rather than a junk value. -/
theorem flow_eq_conductanceOn_mul (P : Kernel Ω Ω) (pi : Measure Ω) {S : Set Ω}
    (hpos : 0 < pi S) (hfin : pi S ≠ ⊤) :
    conductanceOn P pi S * pi S = flow P pi S Sᶜ :=
  ENNReal.div_mul_cancel hpos.ne' hfin

/-- Rescaling `pi` by a positive finite constant multiplies every flow by that
constant. -/
theorem flow_smul_measure (P : Kernel Ω Ω) (pi : Measure Ω) (c : ℝ≥0∞) (S T : Set Ω) :
    flow P (c • pi) S T = c * flow P pi S T := by
  rw [flow, flow, setLIntegral_smul_measure, smul_eq_mul]

/-- **The conductance of a set is invariant under rescaling the measure.**  Both
the numerator and the denominator scale by `c`, and `c` cancels. -/
theorem conductanceOn_smul (P : Kernel Ω Ω) (pi : Measure Ω) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) (S : Set Ω) : conductanceOn P (c • pi) S = conductanceOn P pi S := by
  rw [conductanceOn, conductanceOn, flow_smul_measure, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_div_mul_left _ _ hc0 hct]

/-- The sets the conductance infimum ranges over: measurable sets of positive
measure that are no larger than the threshold `thr`.  The positivity is what
keeps `conductanceOn` from being the junk value `0`; see the module docstring. -/
def SmallSets (pi : Measure Ω) (thr : ℝ≥0∞) : Set (Set Ω) :=
  {S : Set Ω | MeasurableSet S ∧ 0 < pi S ∧ pi S ≤ thr}

/-- Membership in `SmallSets`, unfolded. -/
theorem mem_smallSets_iff {pi : Measure Ω} {thr : ℝ≥0∞} {S : Set Ω} :
    S ∈ SmallSets pi thr ↔ MeasurableSet S ∧ 0 < pi S ∧ pi S ≤ thr := Iff.rfl

/-- The conductance **relative to a threshold** `thr`: the infimum of
`conductanceOn` over the measurable sets of positive measure at most `thr`. -/
noncomputable def conductanceWithin (P : Kernel Ω Ω) (pi : Measure Ω) (thr : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ S ∈ SmallSets pi thr, conductanceOn P pi S

/-- **The conductance** of a Markov chain with kernel `P` and invariant
probability measure `pi`:

`Φ = inf { flow(S, Sᶜ) / pi(S) : S measurable, 0 < pi(S) ≤ 1/2 }`.

The cut-off at `1/2` is the usual one for a probability measure; see
`conductanceWithin` for the version with an explicit threshold. -/
noncomputable def conductance (P : Kernel Ω Ω) (pi : Measure Ω) : ℝ≥0∞ :=
  conductanceWithin P pi (1 / 2)

/-- `conductance` is the infimum in the display of its docstring. -/
theorem conductance_eq_iInf (P : Kernel Ω Ω) (pi : Measure Ω) :
    conductance P pi
      = ⨅ S ∈ {S : Set Ω | MeasurableSet S ∧ 0 < pi S ∧ pi S ≤ 1 / 2}, conductanceOn P pi S :=
  rfl

/-- The conductance is a lower bound for the conductance of any admissible set. -/
theorem conductanceWithin_le_conductanceOn (P : Kernel Ω Ω) (pi : Measure Ω) {thr : ℝ≥0∞}
    {S : Set Ω} (hS : S ∈ SmallSets pi thr) : conductanceWithin P pi thr ≤ conductanceOn P pi S :=
  iInf₂_le S hS

/-- The conductance is a lower bound for the conductance of any measurable set
of measure in `(0, 1/2]`. -/
theorem conductance_le_conductanceOn (P : Kernel Ω Ω) (pi : Measure Ω) {S : Set Ω}
    (hm : MeasurableSet S) (hpos : 0 < pi S) (hhalf : pi S ≤ 1 / 2) :
    conductance P pi ≤ conductanceOn P pi S :=
  conductanceWithin_le_conductanceOn P pi ⟨hm, hpos, hhalf⟩

/-- To bound the conductance from below it suffices to bound every admissible
set. -/
theorem le_conductanceWithin (P : Kernel Ω Ω) (pi : Measure Ω) {thr c : ℝ≥0∞}
    (h : ∀ S ∈ SmallSets pi thr, c ≤ conductanceOn P pi S) : c ≤ conductanceWithin P pi thr :=
  le_iInf₂ h

/-- To bound the conductance from below it suffices to bound every measurable
set of measure in `(0, 1/2]`. -/
theorem le_conductance (P : Kernel Ω Ω) (pi : Measure Ω) {c : ℝ≥0∞}
    (h : ∀ S : Set Ω, MeasurableSet S → 0 < pi S → pi S ≤ 1 / 2 → c ≤ conductanceOn P pi S) :
    c ≤ conductance P pi :=
  le_conductanceWithin P pi fun _ hS => h _ hS.1 hS.2.1 hS.2.2

/-- **The conductance is at most `1`** — provided there is at least one
admissible set.  The hypothesis is not removable: an infimum over the empty
family is `⊤` (`conductance_eq_top_of_isEmpty`), which is exactly the degenerate
situation the caller must rule out. -/
theorem conductance_le_one (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    (h : (SmallSets pi (1 / 2)).Nonempty) : conductance P pi ≤ 1 := by
  obtain ⟨S, hS⟩ := h
  exact (conductanceWithin_le_conductanceOn P pi hS).trans (conductanceOn_le_one P pi S)

/-- If no measurable set has measure in `(0, thr]` then the conductance is `⊤`:
the infimum is over the empty family.  This is the vacuity that
`conductance_le_one` guards against. -/
theorem conductanceWithin_eq_top_of_isEmpty (P : Kernel Ω Ω) (pi : Measure Ω) {thr : ℝ≥0∞}
    (h : SmallSets pi thr = ∅) : conductanceWithin P pi thr = ⊤ := by
  refine le_antisymm le_top (le_conductanceWithin P pi fun S hS => ?_)
  rw [h] at hS
  exact absurd hS (Set.notMem_empty S)

/-- If no measurable set has measure in `(0, 1/2]` then the conductance is `⊤`. -/
theorem conductance_eq_top_of_isEmpty (P : Kernel Ω Ω) (pi : Measure Ω)
    (h : SmallSets pi (1 / 2) = ∅) : conductance P pi = ⊤ :=
  conductanceWithin_eq_top_of_isEmpty P pi h

/-- Rescaling the measure rescales the family of admissible sets by the same
factor. -/
theorem smallSets_smul (pi : Measure Ω) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (thr : ℝ≥0∞) :
    SmallSets (c • pi) (c * thr) = SmallSets pi thr := by
  ext S
  simp only [mem_smallSets_iff, Measure.smul_apply, smul_eq_mul]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(ENNReal.mul_pos_iff.1 h1).2, (ENNReal.mul_le_mul_iff_right hc0 hct).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨ENNReal.mul_pos hc0 h1.ne', (ENNReal.mul_le_mul_iff_right hc0 hct).2 h2⟩

/-- **The conductance is invariant under rescaling the measure**, provided the
threshold is rescaled with it.  Every quotient is scale invariant
(`conductanceOn_smul`) and the family of admissible sets is unchanged
(`smallSets_smul`).

The threshold must move: with the absolute cut-off `1/2` of `conductance` the
statement is false, because rescaling changes which sets are admissible. -/
theorem conductanceWithin_smul (P : Kernel Ω Ω) (pi : Measure Ω) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) (thr : ℝ≥0∞) :
    conductanceWithin P (c • pi) (c * thr) = conductanceWithin P pi thr := by
  rw [conductanceWithin, conductanceWithin, smallSets_smul pi hc0 hct thr]
  exact iInf_congr fun S => iInf_congr fun _ => conductanceOn_smul P pi hc0 hct S

/-! ## A non-vacuity witness

`CLAUDE.md` §11: a hypothesis of the shape `φ ≤ conductance P pi` is worthless
if `conductance` is identically `0`, and `conductance ≤ 1` is worthless if the
infimum is always over the empty family.  The instantly mixing kernel
`Kernel.const Ω pi` — resample from `pi` at every step — settles both: its
conductance is at least `1/2` on any probability space, and on the two-point
space it is *exactly* `1/2`, in particular positive and finite. -/

/-- **The flow of the instantly mixing kernel** `P x = pi` factorises:
`flow(S, T) = pi(T) · pi(S)`. -/
theorem flow_const (pi : Measure Ω) (S T : Set Ω) :
    flow (Kernel.const Ω pi) pi S T = pi T * pi S := by
  simp [flow, Kernel.const_apply]

/-- **The conductance of a set under the instantly mixing kernel** is the mass of
its complement: from anywhere in `S` the next point is a fresh `pi`-sample, so
the chance of escaping is `pi(Sᶜ)`.  Note the `0 < pi S` guard: without it the
quotient is the junk value `0`. -/
theorem conductanceOn_const (pi : Measure Ω) {S : Set Ω} (hpos : 0 < pi S) (hfin : pi S ≠ ⊤) :
    conductanceOn (Kernel.const Ω pi) pi S = pi Sᶜ := by
  rw [conductanceOn, flow_const, ENNReal.mul_div_cancel_right hpos.ne' hfin]

/-- **The instantly mixing kernel has conductance at least `1/2`.**  On every set
of measure at most `1/2` the escape probability is `pi(Sᶜ) = 1 - pi(S) ≥ 1/2`.

This is the concrete computation that makes a hypothesis `φ ≤ conductance P pi`
non-vacuous for `φ ≤ 1/2`. -/
theorem half_le_conductance_const (pi : Measure Ω) [IsProbabilityMeasure pi] :
    1 / 2 ≤ conductance (Kernel.const Ω pi) pi := by
  refine le_conductance _ _ fun S hm hpos hhalf => ?_
  rw [conductanceOn_const pi hpos (measure_ne_top pi S), prob_compl_eq_one_sub hm]
  refine ENNReal.le_sub_of_add_le_right (measure_ne_top pi S) ?_
  calc (1 : ℝ≥0∞) / 2 + pi S ≤ 1 / 2 + 1 / 2 := by gcongr
    _ = 1 := ENNReal.add_halves 1

/-! ### The two-point space -/

/-- The uniform probability measure on the two-point space `Bool`. -/
noncomputable def piHalf : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

/-- `piHalf` gives each of the two points mass `1/2`. -/
@[simp] theorem piHalf_singleton (b : Bool) : piHalf {b} = 1 / 2 := by
  cases b <;> simp [piHalf]

/-- `piHalf` is a probability measure. -/
theorem piHalf_univ : piHalf Set.univ = 1 := by
  have h : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two
  simp [piHalf, h]

instance : IsProbabilityMeasure piHalf := ⟨piHalf_univ⟩

/-- On `Bool` the complement of `{true}` is `{false}`, so it too has mass `1/2`. -/
theorem piHalf_compl_singleton (b : Bool) : piHalf ({b} : Set Bool)ᶜ = 1 / 2 := by
  have h : ({b} : Set Bool)ᶜ = {!b} := by ext c; cases b <;> cases c <;> simp
  rw [h, piHalf_singleton]

/-- `{true}` is an admissible set for the conductance infimum on `Bool`: it is
measurable and has mass exactly `1/2`.  This is what stops
`conductance _ piHalf` from being the empty infimum `⊤`. -/
theorem singleton_mem_smallSets (b : Bool) : ({b} : Set Bool) ∈ SmallSets piHalf (1 / 2) :=
  ⟨measurableSet_singleton b, by rw [piHalf_singleton]; norm_num, (piHalf_singleton b).le⟩

/-- **Non-vacuity witness (`CLAUDE.md` §11).**  On the two-point space with the
uniform measure, the instantly mixing kernel has conductance *exactly* `1/2`.

So `conductance` is a genuinely attained quantity in `(0, 1)`: it is not
identically `0` (which would make every lower bound `φ ≤ conductance` vacuous)
and not identically `⊤` (which would make `conductance ≤ 1` vacuous). -/
theorem conductance_const_piHalf :
    conductance (Kernel.const Bool piHalf) piHalf = 1 / 2 := by
  refine le_antisymm ?_ (half_le_conductance_const piHalf)
  have hmem := singleton_mem_smallSets true
  refine (conductance_le_conductanceOn _ _ hmem.1 hmem.2.1 hmem.2.2).trans_eq ?_
  rw [conductanceOn_const piHalf hmem.2.1 (measure_ne_top piHalf _), piHalf_compl_singleton]

/-- The witness in the form the vacuity check wants: a kernel and a measure whose
conductance is strictly positive and strictly less than `⊤`. -/
theorem exists_conductance_pos :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Kernel Ω Ω) (pi : Measure Ω),
      IsMarkovKernel P ∧ IsProbabilityMeasure pi ∧ Kernel.Invariant P pi ∧
        0 < conductance P pi ∧ conductance P pi ≤ 1 := by
  refine ⟨Bool, inferInstance, Kernel.const Bool piHalf, piHalf, inferInstance, inferInstance,
    (isReversible_const piHalf).invariant, ?_, ?_⟩
  · rw [conductance_const_piHalf]; norm_num
  · exact conductance_le_one _ _ ⟨{true}, singleton_mem_smallSets true⟩

end Arlib.MarkovChains
