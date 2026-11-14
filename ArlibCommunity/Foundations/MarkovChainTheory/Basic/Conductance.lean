/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import ArlibCommunity.Foundations.MarkovChainTheory.Prelude
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
`ArlibCommunity.Foundations.MarkovChainTheory.Basic.Conductance` (which is finite-state and real
valued); everything here is `ℝ≥0∞` valued, so no integrability side conditions
are ever needed.

## Main definitions

* `ArlibCommunity.Foundations.MarkovChainTheory.flow pi P S T = ∫⁻ x in S, P x T ∂pi` — the **ergodic
  flow** from `S` to `T`: the `pi`-probability that one step of the chain starts
  in `S` and lands in `T`.
* `ProbabilityTheory.Kernel.IsReversible P pi` (Mathlib) — **detailed balance**, stated as
  symmetry of the flow on measurable rectangles.
* `ArlibCommunity.Foundations.MarkovChainTheory.conductance pi P S = flow pi P S Sᶜ / pi S` — the
  conductance of a single set: the conditional probability of escaping `S` in
  one step.
* `ArlibCommunity.Foundations.MarkovChainTheory.globalConductanceWithin pi P thr` — the infimum of
  `conductance` over the measurable sets `S` with `0 < pi S ≤ thr`, and
  `ArlibCommunity.Foundations.MarkovChainTheory.globalConductance pi P = globalConductanceWithin pi P (1/2)`, the
  conductance proper.

## Main results

* `flow_univ_right`, `flow_le`, `flow_iUnion`, `flow_mono_left`,
  `flow_mono_right` — the flow calculus.
* `Kernel.IsReversible.invariant` — **detailed balance implies stationarity**.
* `conductance_le_one`, `conductance_lt_top` — `conductance` really is a
  number in `[0,1]` once `0 < pi S < ∞`; it is neither trivially `0` nor `⊤`.
* `conductance_smul`, `globalConductanceWithin_smul` — invariance under rescaling
  the measure.
* `globalConductance_const_piHalf` — the **non-vacuity witness**:
  a concrete kernel and measure whose conductance is provably `1/2`.

## Degenerate values: a warning

`ℝ≥0∞` has `x / 0 = 0`, so `conductance pi P S` is `0` — not `⊤`, not
"undefined" — as soon as `pi S = 0`.  *Every* statement below whose content is
about the size of a conductance therefore carries an explicit `0 < pi S`
hypothesis; without it the statement would be true but empty.  For the same
reason the infimum defining `globalConductance` ranges only over sets of positive
measure, and `globalConductance_le_one` needs the family of such sets to be
non-empty (an infimum over the empty family is `⊤`); see
`globalConductance_eq_top_of_isEmpty` for the converse.

## Design note: the `1/2` threshold and rescaling

`globalConductance` cuts the infimum off at `pi S ≤ 1/2`, as is standard for a
*probability* measure `pi`.  That threshold is an absolute constant, so
`globalConductance (c • pi) P = globalConductance pi` P is **false** in general: rescaling
`pi` by `c` changes which sets are admissible.  What is true, and is proved
here, is that the individual quotients are scale invariant
(`conductance_smul`) and that the infimum is scale invariant once the
threshold is rescaled along with the measure (`globalConductanceWithin_smul`).

## References

The definition is the one used by Lovász–Simonovits and, in the form needed for
the ball walk, by Cousins–Vempala, *Gaussian cooling and `O*(n³)` algorithms for
volume and Gaussian volume*, §4.1.
-/

namespace ArlibCommunity.Foundations.MarkovChainTheory

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The ergodic flow -/

/-- Unfolding lemma for `flow`. -/
theorem flow_apply (pi : Measure Ω) (P : Kernel Ω Ω) (S T : Set Ω) :
    flow pi P S T = ∫⁻ x in S, P x T ∂pi := rfl

/-- Nothing flows out of the empty set. -/
@[simp] theorem flow_empty_left (pi : Measure Ω) (P : Kernel Ω Ω) (T : Set Ω) :
    flow pi P ∅ T = 0 := by
  simp [flow]

/-- Nothing flows into the empty set. -/
@[simp] theorem flow_empty_right (pi : Measure Ω) (P : Kernel Ω Ω) (S : Set Ω) :
    flow pi P S ∅ = 0 := by
  simp [flow]

/-- The flow is monotone in its source set. -/
theorem flow_mono_left (pi : Measure Ω) (P : Kernel Ω Ω) {S S' : Set Ω} (h : S ⊆ S')
    (T : Set Ω) : flow pi P S T ≤ flow pi P S' T :=
  lintegral_mono' (Measure.restrict_mono h le_rfl) le_rfl

/-- The flow is monotone in its target set. -/
theorem flow_mono_right (pi : Measure Ω) (P : Kernel Ω Ω) (S : Set Ω) {T T' : Set Ω}
    (h : T ⊆ T') : flow pi P S T ≤ flow pi P S T' :=
  lintegral_mono fun _ => measure_mono h

/-- The flow is monotone in both arguments. -/
theorem flow_mono (pi : Measure Ω) (P : Kernel Ω Ω) {S S' T T' : Set Ω} (hS : S ⊆ S')
    (hT : T ⊆ T') : flow pi P S T ≤ flow pi P S' T' :=
  (flow_mono_left pi P hS T).trans (flow_mono_right pi P S' hT)

/-- **Everything flows somewhere**: `flow pi P S univ = pi S`.  This is exactly
the statement that `P` is a Markov kernel, and it needs no hypothesis on `pi`. -/
theorem flow_univ_right (pi : Measure Ω) (P : Kernel Ω Ω) [IsMarkovKernel P]  (S : Set Ω) :
    flow pi P S Set.univ = pi S := by
  have h : ∀ x : Ω, P x Set.univ = 1 := fun x => measure_univ
  simp only [flow, h]
  rw [setLIntegral_const, one_mul]

/-- The flow out of `S` never exceeds the mass of `S`. -/
theorem flow_le (pi : Measure Ω) (P : Kernel Ω Ω) [IsMarkovKernel P]  (S T : Set Ω) :
    flow pi P S T ≤ pi S :=
  (flow_mono_right pi P S (Set.subset_univ T)).trans_eq (flow_univ_right pi P S)

/-- **Countable additivity of the flow in its source set.**  For a countable
family of pairwise disjoint measurable sets, the flow out of the union is the
sum of the flows. -/
theorem flow_iUnion (pi : Measure Ω) (P : Kernel Ω Ω) {ι : Type*} [Countable ι]
    {S : ι → Set Ω} (hm : ∀ i, MeasurableSet (S i)) (hd : Pairwise (Function.onFun Disjoint S))
    (T : Set Ω) : flow pi P (⋃ i, S i) T = ∑' i, flow pi P (S i) T :=
  lintegral_iUnion hm hd _

/-- The flow out of `S` splits over a measurable target and its complement. -/
theorem flow_add_flow_compl_right (pi : Measure Ω) (P : Kernel Ω Ω) [IsMarkovKernel P] 
    (S : Set Ω) {T : Set Ω} (hT : MeasurableSet T) :
    flow pi P S T + flow pi P S Tᶜ = pi S := by
  rw [flow, flow, ← lintegral_add_left (Kernel.measurable_coe P hT) _,
    ← flow_univ_right pi P S, flow]
  exact lintegral_congr fun _ => measure_add_measure_compl hT

/-! ## Reversibility

Detailed balance is Mathlib's `ProbabilityTheory.Kernel.IsReversible`.  Read through `flow`
it says that the flow across a measurable rectangle is symmetric
(`flow_comm_of_isReversible`), which is the form the flow calculus below uses. -/

/-- **Detailed balance as symmetry of the flow.**  For a kernel that is reversible with
respect to `pi`, `flow pi P S T = flow pi P T S` on measurable `S`, `T`. -/
theorem flow_comm_of_isReversible {P : Kernel Ω Ω} {pi : Measure Ω}
    (h : Kernel.IsReversible P pi) {S T : Set Ω} (hS : MeasurableSet S)
    (hT : MeasurableSet T) : flow pi P S T = flow pi P T S :=
  h hS hT

/-- **Detailed balance implies stationarity**, in integral form: for a reversible
Markov kernel, `∫ P_x(T) dpi(x) = pi(T)` on every measurable `T`.

The proof is one line of flow calculus: `∫ P_x(T) dpi(x)` is the flow from the
whole space into `T`, reversibility turns it into the flow out of `T` into the
whole space, and that is `pi(T)` because `P` is Markov. -/
theorem lintegral_kernel_apply_of_isReversible {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} (h : Kernel.IsReversible P pi) {T : Set Ω} (hT : MeasurableSet T) :
    ∫⁻ x, P x T ∂pi = pi T := by
  calc ∫⁻ x, P x T ∂pi = flow pi P Set.univ T := by rw [flow, Measure.restrict_univ]
    _ = flow pi P T Set.univ := flow_comm_of_isReversible h MeasurableSet.univ hT
    _ = pi T := flow_univ_right pi P T

/-- **The instantly mixing kernel is reversible.**  For `P x = pi` at every `x`
the flow across a rectangle is the product `pi(T) * pi(S)`, which is symmetric.
This makes `Kernel.IsReversible` non-vacuous. -/
theorem isReversible_const (pi : Measure Ω) : Kernel.IsReversible (Kernel.const Ω pi) pi := by
  intro S T _ _
  simp [Kernel.const_apply, mul_comm]

/-! ## Conductance -/

/-- Unfolding lemma for `conductance`. -/
theorem conductance_apply (pi : Measure Ω) (P : Kernel Ω Ω) (S : Set Ω) :
    conductance pi P S = flow pi P S Sᶜ / pi S := rfl

/-- **A conductance is a probability, hence at most `1`.**  The numerator
`flow pi P S Sᶜ` is bounded by the denominator `pi S` (`flow_le`), so the
quotient is at most `1`.  (At `pi S = 0` both sides are `0 ≤ 1`, by the
`x / 0 = 0` convention; the statement has content exactly when `0 < pi S`, and
`flow_eq_conductance_mul` is the form that says so.) -/
theorem conductance_le_one (pi : Measure Ω) (P : Kernel Ω Ω) [IsMarkovKernel P] 
    (S : Set Ω) : conductance pi P S ≤ 1 :=
  ENNReal.div_le_of_le_mul (by simpa using flow_le pi P S Sᶜ)

/-- **A conductance is finite** as soon as `S` has positive finite measure: the
quotient defining it is a genuine element of `[0,1]`, not `⊤`. -/
theorem conductance_lt_top (pi : Measure Ω) (P : Kernel Ω Ω) [IsMarkovKernel P] 
    {S : Set Ω} (hpos : 0 < pi S) (hfin : pi S ≠ ⊤) : conductance pi P S < ⊤ :=
  ENNReal.div_lt_top ((flow_le pi P S Sᶜ).trans_lt hfin.lt_top).ne hpos.ne'

/-- **No information is lost to the division convention**: for `0 < pi S < ∞`
the conductance really does recover the escape flow,
`Φ(S) · pi(S) = flow`(S, Sᶜ).  Together with `conductance_le_one` this is the
precise sense in which `Φ(S) ∈ [0,1]` is meaningful rather than a junk value. -/
theorem flow_eq_conductance_mul (pi : Measure Ω) (P : Kernel Ω Ω) {S : Set Ω}
    (hpos : 0 < pi S) (hfin : pi S ≠ ⊤) :
    conductance pi P S * pi S = flow pi P S Sᶜ :=
  ENNReal.div_mul_cancel hpos.ne' hfin

/-- Rescaling `pi` by a positive finite constant multiplies every flow by that
constant. -/
theorem flow_smul_measure (pi : Measure Ω) (P : Kernel Ω Ω) (c : ℝ≥0∞) (S T : Set Ω) :
    flow (c • pi) P S T = c * flow pi P S T := by
  rw [flow, flow, setLIntegral_smul_measure, smul_eq_mul]

/-- **The conductance of a set is invariant under rescaling the measure.**  Both
the numerator and the denominator scale by `c`, and `c` cancels. -/
theorem conductance_smul (pi : Measure Ω) (P : Kernel Ω Ω) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) (S : Set Ω) : conductance (c • pi) P S = conductance pi P S := by
  rw [conductance, conductance, flow_smul_measure, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_div_mul_left _ _ hc0 hct]

/-- Membership in `smallSets`, unfolded. -/
theorem mem_smallSets_iff {pi : Measure Ω} {thr : ℝ≥0∞} {S : Set Ω} :
    S ∈ smallSets pi thr ↔ MeasurableSet S ∧ 0 < pi S ∧ pi S ≤ thr := Iff.rfl

/-- `globalConductance` is the infimum in the display of its docstring. -/
theorem globalConductance_eq_iInf (pi : Measure Ω) (P : Kernel Ω Ω) :
    globalConductance pi P
      = ⨅ S ∈ {S : Set Ω | MeasurableSet S ∧ 0 < pi S ∧ pi S ≤ 1 / 2}, conductance pi P S :=
  rfl

/-- The conductance is a lower bound for the conductance of any admissible set. -/
theorem globalConductanceWithin_le_conductance (pi : Measure Ω) (P : Kernel Ω Ω) {thr : ℝ≥0∞}
    {S : Set Ω} (hS : S ∈ smallSets pi thr) : globalConductanceWithin pi P thr ≤ conductance pi P S :=
  iInf₂_le S hS

/-- The conductance is a lower bound for the conductance of any measurable set
of measure in `(0, 1/2]`. -/
theorem globalConductance_le_conductance (pi : Measure Ω) (P : Kernel Ω Ω) {S : Set Ω}
    (hm : MeasurableSet S) (hpos : 0 < pi S) (hhalf : pi S ≤ 1 / 2) :
    globalConductance pi P ≤ conductance pi P S :=
  globalConductanceWithin_le_conductance pi P ⟨hm, hpos, hhalf⟩

/-- To bound the conductance from below it suffices to bound every admissible
set. -/
theorem le_globalConductanceWithin (pi : Measure Ω) (P : Kernel Ω Ω) {thr c : ℝ≥0∞}
    (h : ∀ S ∈ smallSets pi thr, c ≤ conductance pi P S) : c ≤ globalConductanceWithin pi P thr :=
  le_iInf₂ h

/-- To bound the conductance from below it suffices to bound every measurable
set of measure in `(0, 1/2]`. -/
theorem le_globalConductance (pi : Measure Ω) (P : Kernel Ω Ω) {c : ℝ≥0∞}
    (h : ∀ S : Set Ω, MeasurableSet S → 0 < pi S → pi S ≤ 1 / 2 → c ≤ conductance pi P S) :
    c ≤ globalConductance pi P :=
  le_globalConductanceWithin pi P fun _ hS => h _ hS.1 hS.2.1 hS.2.2

/-- **The conductance is at most `1`** — provided there is at least one
admissible set.  The hypothesis is not removable: an infimum over the empty
family is `⊤` (`globalConductance_eq_top_of_isEmpty`), which is exactly the degenerate
situation the caller must rule out. -/
theorem globalConductance_le_one (pi : Measure Ω) (P : Kernel Ω Ω) [IsMarkovKernel P] 
    (h : (smallSets pi (1 / 2)).Nonempty) : globalConductance pi P ≤ 1 := by
  obtain ⟨S, hS⟩ := h
  exact (globalConductanceWithin_le_conductance pi P hS).trans (conductance_le_one pi P S)

/-- If no measurable set has measure in `(0, thr]` then the conductance is `⊤`:
the infimum is over the empty family.  This is the vacuity that
`globalConductance_le_one` guards against. -/
theorem globalConductanceWithin_eq_top_of_isEmpty (pi : Measure Ω) (P : Kernel Ω Ω) {thr : ℝ≥0∞}
    (h : smallSets pi thr = ∅) : globalConductanceWithin pi P thr = ⊤ := by
  refine le_antisymm le_top (le_globalConductanceWithin pi P fun S hS => ?_)
  rw [h] at hS
  exact absurd hS (Set.notMem_empty S)

/-- If no measurable set has measure in `(0, 1/2]` then the conductance is `⊤`. -/
theorem globalConductance_eq_top_of_isEmpty (pi : Measure Ω) (P : Kernel Ω Ω) 
    (h : smallSets pi (1 / 2) = ∅) : globalConductance pi P = ⊤ :=
  globalConductanceWithin_eq_top_of_isEmpty pi P h

/-- Rescaling the measure rescales the family of admissible sets by the same
factor. -/
theorem smallSets_smul (pi : Measure Ω) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (thr : ℝ≥0∞) :
    smallSets (c • pi) (c * thr) = smallSets pi thr := by
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
(`conductance_smul`) and the family of admissible sets is unchanged
(`smallSets_smul`).

The threshold must move: with the absolute cut-off `1/2` of `globalConductance` the
statement is false, because rescaling changes which sets are admissible. -/
theorem globalConductanceWithin_smul (pi : Measure Ω) (P : Kernel Ω Ω) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) (thr : ℝ≥0∞) :
    globalConductanceWithin (c • pi) P (c * thr) = globalConductanceWithin pi P thr := by
  rw [globalConductanceWithin, globalConductanceWithin, smallSets_smul pi hc0 hct thr]
  exact iInf_congr fun S => iInf_congr fun _ => conductance_smul pi P hc0 hct S

/-! ## A non-vacuity witness

The non-vacuity rule: a hypothesis of the shape `φ ≤ globalConductance pi` P is worthless
if `globalConductance` is identically `0`, and `globalConductance ≤ 1` is worthless if the
infimum is always over the empty family.  The instantly mixing kernel
`Kernel.const Ω pi` — resample from `pi` at every step — settles both: its
conductance is at least `1/2` on any probability space, and on the two-point
space it is *exactly* `1/2`, in particular positive and finite. -/

/-- **The flow of the instantly mixing kernel** `P x = pi` factorises:
`flow(S, T) = pi(T) · pi(S)`. -/
theorem flow_const (pi : Measure Ω) (S T : Set Ω) :
    flow pi (Kernel.const Ω pi) S T = pi T * pi S := by
  simp [flow, Kernel.const_apply]

/-- **The conductance of a set under the instantly mixing kernel** is the mass of
its complement: from anywhere in `S` the next point is a fresh `pi`-sample, so
the chance of escaping is `pi(Sᶜ)`.  Note the `0 < pi S` guard: without it the
quotient is the junk value `0`. -/
theorem conductance_const (pi : Measure Ω) {S : Set Ω} (hpos : 0 < pi S) (hfin : pi S ≠ ⊤) :
    conductance pi (Kernel.const Ω pi) S = pi Sᶜ := by
  rw [conductance, flow_const, ENNReal.mul_div_cancel_right hpos.ne' hfin]

/-- **The instantly mixing kernel has conductance at least `1/2`.**  On every set
of measure at most `1/2` the escape probability is `pi(Sᶜ) = 1 - pi(S) ≥ 1/2`.

This is the concrete computation that makes a hypothesis `φ ≤ globalConductance pi` P
non-vacuous for `φ ≤ 1/2`. -/
theorem half_le_globalConductance_const (pi : Measure Ω) [IsProbabilityMeasure pi] :
    1 / 2 ≤ globalConductance pi (Kernel.const Ω pi) := by
  refine le_globalConductance _ _ fun S hm hpos hhalf => ?_
  rw [conductance_const pi hpos (measure_ne_top pi S), prob_compl_eq_one_sub hm]
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
`globalConductance piHalf` _ from being the empty infimum `⊤`. -/
theorem singleton_mem_smallSets (b : Bool) : ({b} : Set Bool) ∈ smallSets piHalf (1 / 2) :=
  ⟨measurableSet_singleton b, by rw [piHalf_singleton]; norm_num, (piHalf_singleton b).le⟩

/-- **Non-vacuity witness.**  On the two-point space with the
uniform measure, the instantly mixing kernel has conductance *exactly* `1/2`.

So `globalConductance` is a genuinely attained quantity in `(0, 1)`: it is not
identically `0` (which would make every lower bound `φ ≤ globalConductance` vacuous)
and not identically `⊤` (which would make `globalConductance ≤ 1` vacuous). -/
theorem globalConductance_const_piHalf :
    globalConductance piHalf (Kernel.const Bool piHalf) = 1 / 2 := by
  refine le_antisymm ?_ (half_le_globalConductance_const piHalf)
  have hmem := singleton_mem_smallSets true
  refine (globalConductance_le_conductance _ _ hmem.1 hmem.2.1 hmem.2.2).trans_eq ?_
  rw [conductance_const piHalf hmem.2.1 (measure_ne_top piHalf _), piHalf_compl_singleton]

/-- The witness in the form the vacuity check wants: a kernel and a measure whose
conductance is strictly positive and strictly less than `⊤`. -/
theorem exists_globalConductance_pos :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Kernel Ω Ω) (pi : Measure Ω),
      IsMarkovKernel P ∧ IsProbabilityMeasure pi ∧ Kernel.Invariant P pi ∧
        0 < globalConductance pi P ∧ globalConductance pi P ≤ 1 := by
  refine ⟨Bool, inferInstance, Kernel.const Bool piHalf, piHalf, inferInstance, inferInstance,
    (isReversible_const piHalf).invariant, ?_, ?_⟩
  · rw [globalConductance_const_piHalf]; norm_num
  · exact globalConductance_le_one _ _ ⟨{true}, singleton_mem_smallSets true⟩

end ArlibCommunity.Foundations.MarkovChainTheory
