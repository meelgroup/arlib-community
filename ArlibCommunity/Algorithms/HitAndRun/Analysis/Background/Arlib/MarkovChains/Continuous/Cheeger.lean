/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.MixingFromConductance
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The `L²` layer: real Dirichlet form, variance, and the spectral gap

`Arlib.MarkovChains.Continuous.MixingFromConductance` stops at
`conductanceOn_eq_dirichletForm_div`, which reads `Φ(S) = E(1_S, 1_S) / π(S)` with `E` the
`ℝ≥0∞`-valued Dirichlet form.  The next object the Cheeger dictionary needs is a
*variance*, and `ℝ≥0∞` is the wrong home for it: `Var f = E f² − (E f)²` truncates at `0`
there.  This module therefore rebuilds the Dirichlet form over `ℝ`, pairs it with Mathlib's
`ProbabilityTheory.variance`, and defines the **spectral gap** as the infimum of the
Rayleigh quotient `E(f,f) / Var(f)`.

## Main definitions

* `Arlib.MarkovChains.dirichletFormReal P pi f = (∫∫ (f x − f y)² dP_x dpi) / 2` — the
  real-valued Dirichlet form.  Unlike the `ℝ≥0∞` version it is a Bochner integral, so
  statements about it carry integrability side conditions; the ones proved here need only
  `MemLp f 2 pi` (or, for indicators, nothing at all beyond finiteness of `pi`).
* `Arlib.MarkovChains.varianceReal pi f` — a thin alias for `ProbabilityTheory.variance f pi`
  with the argument order used throughout this file.  Nothing about variance is reproved;
  the alias exists so that the Rayleigh quotient reads in the order `E / Var`.
* `Arlib.MarkovChains.rayleighQuotient P pi f = dirichletFormReal P pi f / varianceReal pi f`
  and `Arlib.MarkovChains.rayleighSet P pi` — the set of values it takes on the admissible
  `f` (those in `L²(pi)` with nonzero variance).
* `Arlib.MarkovChains.spectralGap P pi = sInf (rayleighSet P pi)`.

## Main results

* `dirichletFormReal_nonneg`, `dirichletFormReal_const`, `dirichletFormReal_add_const` —
  the form is nonnegative, kills constants, and is invariant under adding one.
* `dirichletFormReal_indicator` and **`dirichletFormReal_indicator_of_isReversible`** —
  the bridge to the `ℝ≥0∞` layer: at an indicator the real Dirichlet form is
  `(flow S Sᶜ + flow Sᶜ S).toReal / 2`, and under detailed balance it is exactly
  `(flow S Sᶜ).toReal`.  **This is the load-bearing lemma of the file**: it is what
  connects `spectralGap` to `conductanceOn`.
* `varianceReal_indicator` — `Var(1_S) = π(S) − π(S)²`.
* `spectralGap_nonneg`, `spectralGap_le_rayleighQuotient`, `spectralGap_le_two`.
* **`spectralGap_le_two_mul_conductanceOn`** and
  **`ofReal_spectralGap_le_two_mul_conductance`** — the *easy direction of Cheeger*,
  `gap ≤ 2 Φ`.
* `spectralGap_const`, `spectralGap_const_piHalf` — the non-vacuity witness
  (`CLAUDE.md` §11): for the instantly mixing kernel the Dirichlet form *is* the variance,
  so the spectral gap is exactly `1`; on `Bool` with `piHalf` the conductance is `1/2`
  (`conductance_const_piHalf`), so the easy direction reads `1 ≤ 2 · (1/2)` and is **tight**,
  in particular not vacuous.

## The hard direction: the co-area formula, `L¹` isoperimetry, medians, Cauchy–Schwarz

The later sections build, from scratch, several things Mathlib v4.32 does not have and that
the hard direction of Cheeger runs on.  None of them is a restatement of Cheeger.

* **`lintegral_Ioi_abs_sub_indicator_lt`** — the one-dimensional layer-cake identity
  `∫_{(0,∞)} |1_{t<a} − 1_{t<b}| dt = |a − b|` for `a, b ≥ 0`.
* **`measurable_abs_sub_indicator_lt`** — joint measurability of
  `(t, x, y) ↦ |1_{t < g x} − 1_{t < g y}|` on `ℝ × (Ω × Ω)`.
* **`lintegral_Ioi_flow_add_flow`** — the **co-area formula**: for measurable `g ≥ 0`,
  `∫_0^∞ (flow(S_t, S_tᶜ) + flow(S_tᶜ, S_t)) dt = ∫ |g x − g y| d(pi ⊗ₘ P)` with
  `S_t = {x | t < g x}`.  Proved by `flow_add_flow_compl_eq_lintegral_compProd` plus a
  Tonelli exchange (`lintegral_lintegral_swap`) between the level variable and the pair.
* **`two_mul_conductance_mul_lintegral_le_lintegral_abs_sub`** — the `L¹` isoperimetric
  inequality `2 Φ ∫ g dpi ≤ ∫ |g x − g y| d(pi ⊗ₘ P)` for a reversible chain and a
  measurable `g ≥ 0` supported on a set of measure at most `1/2`.
* **`exists_median`** — every real measurable `f` on a probability space has a level `m`
  with `pi {f > m} ≤ 1/2` and `pi {f < m} ≤ 1/2`.
* **`ofReal_two_mul_dirichletFormReal`** — the `L²`/Bochner bridge
  `ofReal (2 E(g,g)) = ∫⁻ (g x − g y)² d(pi ⊗ₘ P)`, by Fubini for `pi ⊗ₘ P`.  Its
  integrability side condition is discharged, for measurable `g ∈ L²(pi)` and invariant
  `pi`, by `integrable_sq_sub_compProd`.
* **`sq_conductance_mul_lintegral_sq_le_lintegral_sub_sq`** — the `L²` isoperimetric
  inequality `Φ² ∫⁻ g² dpi ≤ ∫⁻ (g x − g y)² d(pi ⊗ₘ P)`, obtained by applying the `L¹`
  inequality to `g²`, factoring `|a² − b²| = |a − b| (a + b)`, and Hölder with `p = q = 2`
  (`ENNReal.lintegral_mul_le_Lp_mul_Lq`).  The `ℝ≥0∞` cancellation is isolated in the
  measure-free `sq_mul_le_of_two_mul_le`.
* **`dirichletFormReal_posPart_add_negPart_le`** — `E(f⁺,f⁺) + E(f⁻,f⁻) ≤ E(f,f)`.
* **`dirichletFormReal_congr_ae`** — the Dirichlet form depends only on the `pi`-a.e. class
  of `f` *when `pi` is invariant*, which is what lets the median argument (which needs a
  measurable `f`) be applied to an arbitrary member of `AdmissibleL2`.

## Main result: `sq_conductance_div_two_le_spectralGap`

**`sq_conductance_div_two_le_spectralGap`** — the **hard direction of Cheeger**:

`(conductance P pi).toReal ^ 2 / 2 ≤ spectralGap P pi`

for a reversible Markov kernel on a probability space, under the single hypothesis
`(rayleighSet P pi).Nonempty` (some `L²` function has nonzero variance).  That hypothesis is
forced by the design note below — `sInf ∅ = 0` over `ℝ` — and is *not* a disguised form of
the conclusion: it mentions neither the conductance nor any isoperimetric constant.
`rayleighSet_const_piHalf_nonempty` and `sq_conductance_div_two_le_spectralGap_const_piHalf`
exhibit a chain satisfying it, on which the inequality reads `1/8 ≤ 1`.

**`cheeger`** packages both directions: `Φ²/2 ≤ gap ≤ 2 Φ`.

There is no `def`, `structure` field or predicate anywhere in this file that names the
Cheeger inequality (or isoperimetry) and stands in for its proof.  That failure mode — a
predicate whose name asserts the theorem — is what `CLAUDE.md` §11 and `CV-ROADMAP.md` §2a
warn about, and what `../gaussian-cooling-vempala`'s `Isoperimetry` / `MixingFromConductance` /
`SpeedyConductance` / `BallWalkMixing` exhibit.

## What is still NOT here

The geometric decay bound `d_TV ≤ √M (1 − phi²/2)^t` is *not* derived: going from a spectral
gap to a total-variation decay rate needs the `L²` → TV comparison (a warm-start / density
bound), which this file does not develop.  `mixesWithin_of_conductance_decay`'s `hdecay`
hypothesis therefore still remains the caller's obligation.

## Design note: why `sInf` of an image and not `⨅ f ∈ s`

Over `ℝ≥0∞` the idiom `⨅ f ∈ s, g f` is correct because the inner `⨅ _ : f ∈ s, g f` is `⊤`
— the neutral element — when `f ∉ s`.  Over `ℝ` it is `sInf ∅ = 0` instead, so
`⨅ f ∈ s, g f` collapses to `0` as soon as a single `f` fails to lie in `s`.  The spectral
gap is therefore defined as `sInf` of the *image* of the admissible set, which is the
intended quantity.  `BddBelow` (by `0`, `bddBelow_rayleighSet`) is what makes `csInf_le`
usable; note that `sInf ∅ = 0` still means `spectralGap = 0` on a space with no admissible
`f` at all, which is why the non-vacuity witness computes an actual positive value.

## References

* Lovász–Simonovits, *Random walks in a convex body and an improved volume algorithm*,
  RSA 1993.
* Cousins–Vempala, *Gaussian cooling and `O*(n³)` algorithms for volume and Gaussian
  volume*, §4.1.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The real-valued Dirichlet form -/

/-- The **real Dirichlet form** of `f`:

`E(f, f) = (1/2) ∫∫ (f x − f y)² dP_x(y) dpi(x)`.

This is the `ℝ`-valued counterpart of `Arlib.MarkovChains.dirichletForm`.  The `ℝ≥0∞`
version needs no integrability hypotheses but cannot be paired with a variance; this one
can, at the price of carrying `MemLp f 2 pi` wherever the value matters.  Note that the
definition itself is total: for a non-integrable `f` the Bochner integral is `0` by
convention, so every lemma below that has content states its integrability hypothesis
explicitly. -/
noncomputable def dirichletFormReal (P : Kernel Ω Ω) (pi : Measure Ω) (f : Ω → ℝ) : ℝ :=
  (∫ x, ∫ y, (f x - f y) ^ 2 ∂(P x) ∂pi) / 2

/-- Unfolding lemma for `dirichletFormReal`. -/
theorem dirichletFormReal_apply (P : Kernel Ω Ω) (pi : Measure Ω) (f : Ω → ℝ) :
    dirichletFormReal P pi f = (∫ x, ∫ y, (f x - f y) ^ 2 ∂(P x) ∂pi) / 2 := rfl

/-- **The Dirichlet form is nonnegative.**  No hypothesis at all: the integrand is a square,
and the Bochner integral of a nonnegative function is nonnegative even when the function is
not integrable (the junk value is `0`). -/
theorem dirichletFormReal_nonneg (P : Kernel Ω Ω) (pi : Measure Ω) (f : Ω → ℝ) :
    0 ≤ dirichletFormReal P pi f :=
  div_nonneg (integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _) (by norm_num)

/-- **A constant function has zero Dirichlet energy.** -/
@[simp] theorem dirichletFormReal_const (P : Kernel Ω Ω) (pi : Measure Ω) (c : ℝ) :
    dirichletFormReal P pi (fun _ => c) = 0 := by
  simp [dirichletFormReal]

/-- **The Dirichlet form is invariant under adding a constant.**  This is what makes the
Rayleigh quotient `E / Var` well posed: the variance has the same invariance. -/
theorem dirichletFormReal_add_const (P : Kernel Ω Ω) (pi : Measure Ω) (f : Ω → ℝ) (c : ℝ) :
    dirichletFormReal P pi (fun x => f x + c) = dirichletFormReal P pi f := by
  simp only [dirichletFormReal, add_sub_add_right_eq_sub]

/-! ## The bridge to the `ℝ≥0∞` layer: the form at an indicator

This is the load-bearing computation of the file.  `conductanceOn` is defined out of `flow`,
which is an `ℝ≥0∞` lower integral; `spectralGap` is defined out of `dirichletFormReal`,
which is a Bochner integral.  The two are connected here, at indicators, which is exactly
where the easy direction of Cheeger evaluates the Rayleigh quotient. -/

/-- **The inner integral of the real Dirichlet form at an indicator.**  From a point of `S`
the squared increment `(1_S x − 1_S y)²` is the indicator of `Sᶜ` in `y`, and vice versa;
integrating against `P x` therefore returns the escape probability `P x Sᶜ` on `S` and the
entry probability `P x S` off `S`.

This is the `ℝ`-valued twin of `lintegral_kernel_sub_indicator_sq`. -/
theorem integral_kernel_sub_indicator_sq (P : Kernel Ω Ω) {S : Set Ω} (hS : MeasurableSet S)
    (x : Ω) :
    ∫ y, (Set.indicator S (fun _ => (1 : ℝ)) x
        - Set.indicator S (fun _ => (1 : ℝ)) y) ^ 2 ∂(P x)
      = Set.indicator S (fun x => (P x Sᶜ).toReal) x
        + Set.indicator Sᶜ (fun x => (P x S).toReal) x := by
  by_cases hx : x ∈ S
  · have hrw : (fun y => (Set.indicator S (fun _ => (1 : ℝ)) x
        - Set.indicator S (fun _ => (1 : ℝ)) y) ^ 2)
        = Set.indicator Sᶜ (fun _ => (1 : ℝ)) := by
      funext y
      by_cases hy : y ∈ S <;> simp [hx, hy]
    rw [hrw, integral_indicator_const (1 : ℝ) hS.compl]
    simp [hx, measureReal_def]
  · have hrw : (fun y => (Set.indicator S (fun _ => (1 : ℝ)) x
        - Set.indicator S (fun _ => (1 : ℝ)) y) ^ 2)
        = Set.indicator S (fun _ => (1 : ℝ)) := by
      funext y
      by_cases hy : y ∈ S <;> simp [hx, hy]
    rw [hrw, integral_indicator_const (1 : ℝ) hS]
    simp [hx, measureReal_def]

/-- The outer integrand of the Dirichlet form at an indicator is integrable: it is
measurable and bounded by `1`, and `pi` is finite. -/
theorem integrable_indicator_kernel_toReal (P : Kernel Ω Ω) [IsMarkovKernel P]
    (pi : Measure Ω) [IsFiniteMeasure pi] {S T : Set Ω} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    Integrable (Set.indicator S (fun x => (P x T).toReal)) pi := by
  refine Integrable.of_bound
    (((Kernel.measurable_coe P hT).ennreal_toReal.indicator hS).aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  · simp [hx]

/-- **The outer integral of the Dirichlet form at an indicator is a flow.**  Restricting to
`S` and pushing `toReal` through the integral (legitimate because `P x T ≤ 1 < ⊤`) turns the
Bochner integral into `Arlib.MarkovChains.flow`. -/
theorem integral_indicator_kernel_toReal (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∫ x, Set.indicator S (fun x => (P x T).toReal) x ∂pi = (flow P pi S T).toReal := by
  rw [integral_indicator hS, flow]
  exact integral_toReal (Kernel.measurable_coe P hT).aemeasurable
    (Filter.Eventually.of_forall fun x => measure_lt_top (P x) T)

/-- **The bridge, symmetric form.**  At an indicator the real Dirichlet form is the
symmetrised ergodic flow — the `toReal` of `dirichletForm_indicator`. -/
theorem dirichletFormReal_indicator (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    [IsFiniteMeasure pi] {S : Set Ω} (hS : MeasurableSet S) :
    dirichletFormReal P pi (Set.indicator S (fun _ => (1 : ℝ)))
      = ((flow P pi S Sᶜ).toReal + (flow P pi Sᶜ S).toReal) / 2 := by
  rw [dirichletFormReal]
  congr 1
  rw [integral_congr_ae (Filter.Eventually.of_forall (integral_kernel_sub_indicator_sq P hS)),
    integral_add (integrable_indicator_kernel_toReal P pi hS hS.compl)
      (integrable_indicator_kernel_toReal P pi hS.compl hS),
    integral_indicator_kernel_toReal P pi hS hS.compl,
    integral_indicator_kernel_toReal P pi hS.compl hS]

/-- **The bridge (`item 1` of the brief).**  For a reversible chain the real Dirichlet form
at an indicator is the escape flow:

`E(1_S, 1_S) = (flow P pi S Sᶜ).toReal`.

Together with `varianceReal_indicator` below this is what lets the Rayleigh quotient at an
indicator be compared with `conductanceOn`, and hence what connects `spectralGap` to
`conductance`.  It is the real-valued twin of `dirichletForm_indicator_of_isReversible`. -/
theorem dirichletFormReal_indicator_of_isReversible {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsFiniteMeasure pi] (hrev : IsReversible P pi) {S : Set Ω}
    (hS : MeasurableSet S) :
    dirichletFormReal P pi (Set.indicator S (fun _ => (1 : ℝ))) = (flow P pi S Sᶜ).toReal := by
  rw [dirichletFormReal_indicator P pi hS, ← hrev S Sᶜ hS hS.compl]
  ring

/-! ## Variance

Nothing about variance is developed from scratch: `ProbabilityTheory.variance` already fits,
and `varianceReal` is a *definitional* alias for it whose only purpose is to put the measure
first, so that the Rayleigh quotient below reads `dirichletFormReal P pi f / varianceReal pi f`
with the measure in the same position in both factors.  Every lemma in this section is a
restatement or a one-line consequence of Mathlib's. -/

/-- The **variance** of `f` under `pi`, `∫ f² dpi − (∫ f dpi)²`.  This is exactly
`ProbabilityTheory.variance f pi`; see `varianceReal_eq_variance` and `varianceReal_eq_sub`. -/
noncomputable def varianceReal (pi : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ProbabilityTheory.variance f pi

/-- `varianceReal` is Mathlib's `ProbabilityTheory.variance`, arguments swapped. -/
theorem varianceReal_eq_variance (pi : Measure Ω) (f : Ω → ℝ) :
    varianceReal pi f = ProbabilityTheory.variance f pi := rfl

/-- **The variance is nonnegative** (`ProbabilityTheory.variance_nonneg`). -/
theorem varianceReal_nonneg (pi : Measure Ω) (f : Ω → ℝ) : 0 ≤ varianceReal pi f :=
  ProbabilityTheory.variance_nonneg f pi

/-- **`Var f = ∫ f² − (∫ f)²`**, the form named in the definition's docstring.  Needs
`MemLp f 2` — without it both sides are junk values and the identity is false in general. -/
theorem varianceReal_eq_sub {pi : Measure Ω} [IsProbabilityMeasure pi] {f : Ω → ℝ}
    (hf : MemLp f 2 pi) :
    varianceReal pi f = (∫ x, f x ^ 2 ∂pi) - (∫ x, f x ∂pi) ^ 2 :=
  ProbabilityTheory.variance_eq_sub hf

/-- A constant function has zero variance. -/
@[simp] theorem varianceReal_const (pi : Measure Ω) [IsProbabilityMeasure pi] (c : ℝ) :
    varianceReal pi (fun _ => c) = 0 := by
  simp [varianceReal, ProbabilityTheory.variance, ProbabilityTheory.evariance]

/-- **The variance vanishes exactly on the a.e. constant functions.**  Both directions;
the forward one is Mathlib's `ae_eq_integral_of_variance_eq_zero`. -/
theorem varianceReal_eq_zero_iff {pi : Measure Ω} [IsProbabilityMeasure pi] {f : Ω → ℝ}
    (hf : MemLp f 2 pi) :
    varianceReal pi f = 0 ↔ f =ᵐ[pi] fun _ => ∫ x, f x ∂pi := by
  refine ⟨fun h => ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hf h, fun h => ?_⟩
  rw [varianceReal, ProbabilityTheory.variance_congr h]
  exact varianceReal_const pi _

/-- **The variance of an indicator**: `Var(1_S) = pi(S) − pi(S)²`, i.e. `p (1 − p)`. -/
theorem varianceReal_indicator {pi : Measure Ω} [IsProbabilityMeasure pi] {S : Set Ω}
    (hS : MeasurableSet S) :
    varianceReal pi (Set.indicator S (fun _ => (1 : ℝ)))
      = (pi S).toReal - (pi S).toReal ^ 2 := by
  have hmem : MemLp (Set.indicator S (fun _ => (1 : ℝ))) 2 pi :=
    (memLp_const (1 : ℝ)).indicator hS
  have hsq : ∀ x : Ω, Set.indicator S (fun _ => (1 : ℝ)) x ^ 2
      = Set.indicator S (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [varianceReal_eq_sub hmem]
  simp only [hsq]
  rw [integral_indicator_const (1 : ℝ) hS]
  simp [measureReal_def]

/-- The indicator of a measurable set is in `L²` of a finite measure. -/
theorem memLp_two_indicator {pi : Measure Ω} [IsFiniteMeasure pi] {S : Set Ω}
    (hS : MeasurableSet S) : MemLp (Set.indicator S (fun _ => (1 : ℝ))) 2 pi :=
  (memLp_const (1 : ℝ)).indicator hS

/-! ## The spectral gap -/

/-- The functions the spectral-gap infimum ranges over: those in `L²(pi)` whose variance
does not vanish.  The variance condition is what keeps the Rayleigh quotient from being the
junk value `x / 0 = 0`, and by `varianceReal_eq_zero_iff` it excludes exactly the a.e.
constant functions — on which the Dirichlet form vanishes too, so `0/0` would otherwise
force `spectralGap = 0` on every chain. -/
def AdmissibleL2 (pi : Measure Ω) : Set (Ω → ℝ) :=
  {f : Ω → ℝ | MemLp f 2 pi ∧ varianceReal pi f ≠ 0}

/-- Membership in `AdmissibleL2`, unfolded. -/
theorem mem_admissibleL2_iff {pi : Measure Ω} {f : Ω → ℝ} :
    f ∈ AdmissibleL2 pi ↔ MemLp f 2 pi ∧ varianceReal pi f ≠ 0 := Iff.rfl

/-- The **Rayleigh quotient** `E(f, f) / Var(f)` of the chain at `f`. -/
noncomputable def rayleighQuotient (P : Kernel Ω Ω) (pi : Measure Ω) (f : Ω → ℝ) : ℝ :=
  dirichletFormReal P pi f / varianceReal pi f

/-- The Rayleigh quotient is nonnegative: both the Dirichlet form and the variance are. -/
theorem rayleighQuotient_nonneg (P : Kernel Ω Ω) (pi : Measure Ω) (f : Ω → ℝ) :
    0 ≤ rayleighQuotient P pi f :=
  div_nonneg (dirichletFormReal_nonneg P pi f) (varianceReal_nonneg pi f)

/-- The set of values of the Rayleigh quotient on the admissible functions. -/
noncomputable def rayleighSet (P : Kernel Ω Ω) (pi : Measure Ω) : Set ℝ :=
  rayleighQuotient P pi '' AdmissibleL2 pi

/-- The **spectral gap** of a reversible chain: the infimum of the Rayleigh quotient
`E(f,f) / Var(f)` over `f ∈ L²(pi)` of nonzero variance.

See the module docstring for why this is `sInf` of an image rather than the more idiomatic
`⨅ f ∈ _, _`: over `ℝ` the latter collapses to `0`. -/
noncomputable def spectralGap (P : Kernel Ω Ω) (pi : Measure Ω) : ℝ :=
  sInf (rayleighSet P pi)

/-- The Rayleigh values are bounded below by `0`, which is what makes `csInf_le` available. -/
theorem bddBelow_rayleighSet (P : Kernel Ω Ω) (pi : Measure Ω) : BddBelow (rayleighSet P pi) := by
  refine ⟨0, ?_⟩
  rintro r ⟨f, -, rfl⟩
  exact rayleighQuotient_nonneg P pi f

/-- **The spectral gap is nonnegative.**  (Also when the admissible family is empty: then the
infimum is the junk value `sInf ∅ = 0`.) -/
theorem spectralGap_nonneg (P : Kernel Ω Ω) (pi : Measure Ω) : 0 ≤ spectralGap P pi := by
  refine Real.sInf_nonneg ?_
  rintro r ⟨f, -, rfl⟩
  exact rayleighQuotient_nonneg P pi f

/-- **The spectral gap is a lower bound for every admissible Rayleigh quotient.** -/
theorem spectralGap_le_rayleighQuotient (P : Kernel Ω Ω) (pi : Measure Ω) {f : Ω → ℝ}
    (hf : MemLp f 2 pi) (hv : varianceReal pi f ≠ 0) :
    spectralGap P pi ≤ rayleighQuotient P pi f :=
  csInf_le (bddBelow_rayleighSet P pi) ⟨f, ⟨hf, hv⟩, rfl⟩

/-- To bound the spectral gap from below it suffices to bound every admissible quotient. -/
theorem le_spectralGap (P : Kernel Ω Ω) (pi : Measure Ω) {c : ℝ}
    (hne : (rayleighSet P pi).Nonempty)
    (h : ∀ f : Ω → ℝ, MemLp f 2 pi → varianceReal pi f ≠ 0 → c ≤ rayleighQuotient P pi f) :
    c ≤ spectralGap P pi := by
  refine le_csInf hne ?_
  rintro r ⟨f, ⟨hf, hv⟩, rfl⟩
  exact h f hf hv

/-! ## The easy direction of Cheeger: `gap ≤ 2 Φ`

Evaluate the Rayleigh quotient at `f = 1_S` for a set of measure `p ∈ (0, 1/2]`.  The
numerator is the escape flow `Φ(S) · p` (`dirichletFormReal_indicator_of_isReversible`), the
denominator is `p(1 − p) ≥ p/2` (`varianceReal_indicator`), so the quotient is
`Φ(S)/(1 − p) ≤ 2 Φ(S)`.  Taking the infimum over `S` gives the bound against the
conductance. -/

/-- **The easy direction of Cheeger, at a single set.**  For a reversible chain and a
measurable `S` with `0 < pi S ≤ 1/2`,

`spectralGap P pi ≤ 2 · Φ(S)`.

The proof is the indicator computation: `E(1_S,1_S) = Φ(S) · pi(S)` and
`Var(1_S) = pi(S)(1 − pi(S)) ≥ pi(S)/2`. -/
theorem spectralGap_le_two_mul_conductanceOn {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {S : Set Ω}
    (hS : MeasurableSet S) (hpos : 0 < pi S) (hhalf : pi S ≤ 1 / 2) :
    spectralGap P pi ≤ 2 * (conductanceOn P pi S).toReal := by
  set p : ℝ := (pi S).toReal with hp
  set phi : ℝ := (conductanceOn P pi S).toReal with hphi
  have hpfin : pi S ≠ ⊤ := measure_ne_top pi S
  have hp0 : 0 < p := ENNReal.toReal_pos hpos.ne' hpfin
  have hphalf : p ≤ 1 / 2 := by
    have h2 : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by norm_num
    exact h2 ▸ ENNReal.toReal_mono (by norm_num) hhalf
  have hphi0 : 0 ≤ phi := ENNReal.toReal_nonneg
  -- the numerator
  have hnum : dirichletFormReal P pi (Set.indicator S (fun _ => (1 : ℝ))) = phi * p := by
    rw [dirichletFormReal_indicator_of_isReversible hrev hS,
      ← flow_eq_conductanceOn_mul P pi hpos hpfin, ENNReal.toReal_mul]
  -- the denominator
  have hden : varianceReal pi (Set.indicator S (fun _ => (1 : ℝ))) = p - p ^ 2 :=
    varianceReal_indicator hS
  have hdenpos : 0 < p - p ^ 2 := by nlinarith
  refine (spectralGap_le_rayleighQuotient P pi (memLp_two_indicator hS)
    (by rw [hden]; exact hdenpos.ne')).trans ?_
  rw [rayleighQuotient, hnum, hden, div_le_iff₀ hdenpos]
  nlinarith [mul_nonneg (mul_nonneg hphi0 hp0.le) (by linarith : (0 : ℝ) ≤ 1 - 2 * p)]

/-- **The easy direction of Cheeger.**  `gap ≤ 2 Φ`, with both sides read in `ℝ≥0∞`.

Stated as `ENNReal.ofReal (spectralGap P pi) ≤ 2 * conductance P pi` because `spectralGap`
lives in `ℝ` and `conductance` in `ℝ≥0∞`; `spectralGap_le_two_mul_conductanceOn` is the
per-set form with no coercion.  When no measurable set has measure in `(0, 1/2]` the right
side is `⊤` (`conductance_eq_top_of_isEmpty`) and the statement is empty — which is the
degenerate case the non-vacuity witness `spectralGap_const_piHalf` rules out. -/
theorem ofReal_spectralGap_le_two_mul_conductance {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi) :
    ENNReal.ofReal (spectralGap P pi) ≤ 2 * conductance P pi := by
  have key : ENNReal.ofReal (spectralGap P pi) / 2 ≤ conductance P pi := by
    refine le_conductance P pi fun S hS hpos hhalf => ?_
    refine ENNReal.div_le_of_le_mul ?_
    have hle := spectralGap_le_two_mul_conductanceOn hrev hS hpos hhalf
    have hfin : conductanceOn P pi S ≠ ⊤ :=
      (conductanceOn_lt_top P pi hpos (measure_ne_top pi S)).ne
    calc ENNReal.ofReal (spectralGap P pi)
        ≤ ENNReal.ofReal (2 * (conductanceOn P pi S).toReal) := ENNReal.ofReal_le_ofReal hle
      _ = conductanceOn P pi S * 2 := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hfin]
          rw [mul_comm]
          norm_num
  calc ENNReal.ofReal (spectralGap P pi)
      = ENNReal.ofReal (spectralGap P pi) / 2 * 2 :=
        (ENNReal.div_mul_cancel (by norm_num) (by norm_num)).symm
    _ ≤ conductance P pi * 2 := by gcongr
    _ = 2 * conductance P pi := mul_comm _ _

/-- **The spectral gap is at most `2`** — provided at least one measurable set has measure in
`(0, 1/2]`, which is what makes the conductance infimum non-empty.  Immediate from the easy
direction and `conductanceOn_le_one`. -/
theorem spectralGap_le_two {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {S : Set Ω} (hS : MeasurableSet S)
    (hpos : 0 < pi S) (hhalf : pi S ≤ 1 / 2) : spectralGap P pi ≤ 2 := by
  refine (spectralGap_le_two_mul_conductanceOn hrev hS hpos hhalf).trans ?_
  have h1 : (conductanceOn P pi S).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using conductanceOn_le_one P pi S)
  linarith

/-! ## A non-vacuity witness (`CLAUDE.md` §11)

`spectralGap` is an infimum over a family that could be empty, and `sInf ∅ = 0` in `ℝ`; a
bound `spectralGap ≤ 2 Φ` would then say nothing.  The instantly mixing kernel
`Kernel.const Ω pi` settles this: for it the Dirichlet form *is* the variance, so the
Rayleigh quotient is identically `1` and `spectralGap = 1` whenever a single admissible `f`
exists.  On `Bool` with `piHalf` the conductance of that same kernel is exactly `1/2`
(`conductance_const_piHalf`), so the easy direction reads `1 ≤ 2 · (1/2)` — an equality, so
the inequality is not merely non-vacuous but **tight**. -/

/-- **For the instantly mixing kernel the Dirichlet form is the variance.**

`E(f,f) = (1/2) ∫∫ (f x − f y)² dpi dpi = ∫ f² − (∫ f)²`.

Expanding the square and integrating twice is all that happens; the `MemLp f 2` hypothesis
is what makes both `f` and `f²` integrable so that linearity applies. -/
theorem dirichletFormReal_const_kernel {pi : Measure Ω} [IsProbabilityMeasure pi] {f : Ω → ℝ}
    (hf : MemLp f 2 pi) :
    dirichletFormReal (Kernel.const Ω pi) pi f = varianceReal pi f := by
  have hint : Integrable f pi := hf.integrable (by norm_num)
  have hsq : Integrable (fun x => f x ^ 2) pi := hf.integrable_sq
  set m : ℝ := ∫ x, f x ∂pi with hm
  set M : ℝ := ∫ x, f x ^ 2 ∂pi with hM
  have hinner : ∀ x : Ω, ∫ y, (f x - f y) ^ 2 ∂((Kernel.const Ω pi) x)
      = f x ^ 2 - 2 * f x * m + M := by
    intro x
    have hlin : Integrable (fun y => (2 * f x) * f y) pi := hint.const_mul _
    have hA : Integrable (fun y => f x ^ 2 - (2 * f x) * f y) pi :=
      (integrable_const _).sub hlin
    have h1 : (fun y => (f x - f y) ^ 2)
        = fun y => (f x ^ 2 - (2 * f x) * f y) + f y ^ 2 := by funext y; ring
    rw [Kernel.const_apply, h1, integral_add hA hsq,
      integral_sub (integrable_const _) hlin, integral_const, integral_const_mul, ← hm, ← hM]
    simp
  rw [dirichletFormReal, integral_congr_ae (Filter.Eventually.of_forall hinner)]
  have hlin' : Integrable (fun x => (2 * m) * f x) pi := hint.const_mul _
  have hB : Integrable (fun x => f x ^ 2 - (2 * m) * f x) pi := hsq.sub hlin'
  have h2 : (fun x => f x ^ 2 - 2 * f x * m + M)
      = fun x => (f x ^ 2 - (2 * m) * f x) + M := by funext x; ring
  rw [h2, integral_add hB (integrable_const M), integral_sub hsq hlin', integral_const_mul,
    integral_const, varianceReal_eq_sub hf, ← hm, ← hM]
  simp
  ring

/-- **The Rayleigh quotient of the instantly mixing kernel is identically `1`.** -/
theorem rayleighQuotient_const_kernel {pi : Measure Ω} [IsProbabilityMeasure pi] {f : Ω → ℝ}
    (hf : MemLp f 2 pi) (hv : varianceReal pi f ≠ 0) :
    rayleighQuotient (Kernel.const Ω pi) pi f = 1 := by
  rw [rayleighQuotient, dirichletFormReal_const_kernel hf, div_self hv]

/-- **The spectral gap of the instantly mixing kernel is `1`** — as soon as there is a
single `L²` function of nonzero variance to take the infimum over. -/
theorem spectralGap_const {pi : Measure Ω} [IsProbabilityMeasure pi]
    (h : ∃ f : Ω → ℝ, MemLp f 2 pi ∧ varianceReal pi f ≠ 0) :
    spectralGap (Kernel.const Ω pi) pi = 1 := by
  obtain ⟨f, hf, hv⟩ := h
  refine le_antisymm ((spectralGap_le_rayleighQuotient _ _ hf hv).trans_eq
    (rayleighQuotient_const_kernel hf hv)) ?_
  refine le_spectralGap _ _ ⟨1, ⟨f, ⟨hf, hv⟩, rayleighQuotient_const_kernel hf hv⟩⟩ ?_
  intro g hg hgv
  exact (rayleighQuotient_const_kernel hg hgv).ge

/-- On `Bool` with the uniform measure, `1_{true}` is an `L²` function of variance `1/4`;
in particular the spectral-gap infimum is over a non-empty family. -/
theorem varianceReal_indicator_piHalf :
    varianceReal piHalf (Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ))) = 1 / 4 := by
  rw [varianceReal_indicator (measurableSet_singleton true), piHalf_singleton]
  norm_num

/-- **Non-vacuity witness (`CLAUDE.md` §11).**  On the two-point space with the uniform
measure the instantly mixing kernel has spectral gap exactly `1`.  So `spectralGap` is a
genuinely attained positive quantity, not the junk value `sInf ∅ = 0`. -/
theorem spectralGap_const_piHalf :
    spectralGap (Kernel.const Bool piHalf) piHalf = 1 := by
  refine spectralGap_const ⟨Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)),
    memLp_two_indicator (measurableSet_singleton true), ?_⟩
  rw [varianceReal_indicator_piHalf]
  norm_num

/-- **The easy direction is tight, and not vacuous.**  For `Kernel.const Bool piHalf` the
spectral gap is `1` (`spectralGap_const_piHalf`), the conductance is `1/2`
(`conductance_const_piHalf`), and `ofReal_spectralGap_le_two_mul_conductance` reads
`1 ≤ 2 · (1/2)` — with equality.

This is the check `CLAUDE.md` §11 asks for: the inequality relates two quantities that are
both computed, both finite, and both nonzero on a concrete chain. -/
theorem spectralGap_eq_two_mul_conductance_const_piHalf :
    ENNReal.ofReal (spectralGap (Kernel.const Bool piHalf) piHalf)
      = 2 * conductance (Kernel.const Bool piHalf) piHalf := by
  rw [spectralGap_const_piHalf, conductance_const_piHalf, ENNReal.ofReal_one, mul_one_div,
    ENNReal.div_self (by norm_num) (by norm_num)]

/-- The witness in the form the vacuity check wants: a reversible chain on which the
spectral gap, the conductance and the easy direction of Cheeger are all simultaneously
non-degenerate. -/
theorem exists_spectralGap_pos :
    ∃ (Om : Type) (_ : MeasurableSpace Om) (P : Kernel Om Om) (pi : Measure Om),
      IsMarkovKernel P ∧ IsProbabilityMeasure pi ∧ IsReversible P pi ∧
        0 < spectralGap P pi ∧ conductance P pi = 1 / 2 ∧
        ENNReal.ofReal (spectralGap P pi) ≤ 2 * conductance P pi := by
  refine ⟨Bool, inferInstance, Kernel.const Bool piHalf, piHalf, inferInstance, inferInstance,
    isReversible_const piHalf, ?_, conductance_const_piHalf, ?_⟩
  · rw [spectralGap_const_piHalf]; norm_num
  · exact spectralGap_eq_two_mul_conductance_const_piHalf.le

/-! ## The hard direction — the road map

Every lemma from here to the end is stated and proved on its own terms; **no name and no
statement in this file asserts anything about the spectral gap, the conductance or an
isoperimetric constant that is not proved**, and there is no hypothesis-bundling `structure`
at all.

Given `f` with `Var f ≠ 0`, pick a median `m` (`exists_median`) and split `f − m` into its
positive and negative parts `g, h ≥ 0`, each supported on a set of `pi`-measure at most
`1/2`.

1. `Var f ≤ ∫ (f − m)² = ∫ g² + ∫ h²` — `varianceReal_le_integral_sub_sq` below plus
   `sq_max_zero_add_sq_max_neg_zero`.
2. `E(f,f) ≥ E(g,g) + E(h,h)` — pointwise from `sq_posPart_sub_add_sq_negPart_sub_le` below;
   the integration is done in `ℝ≥0∞` (where `lintegral_mono` needs no side condition) and
   returned to `ℝ` by the bridge, in `dirichletFormReal_posPart_add_negPart_le`.
3. **The co-area step**, for `g ≥ 0` with `pi {g > 0} ≤ 1/2`:
   `∫∫ |g(x) − g(y)| d(pi ⊗ₘ P) = ∫_0^∞ (flow(S_t, S_tᶜ) + flow(S_tᶜ, S_t)) dt
   ≥ 2 phi ∫_0^∞ pi(S_t) dt = 2 phi ∫ g dpi`, with `S_t = {x | t < g x}` —
   `lintegral_Ioi_flow_add_flow` (the identity) and
   `two_mul_conductance_mul_lintegral_le_lintegral_abs_sub` (the inequality).  Applied to
   `g²` in place of `g` this is the `2 phi ∫ g²` the argument wants.
4. Cauchy–Schwarz: `∫∫ |g(x)² − g(y)²| ≤ (∫∫ (g x − g y)²)^{1/2} (∫∫ (g x + g y)²)^{1/2}
   ≤ (2 E(g,g))^{1/2} (4 ∫ g²)^{1/2}`, whence `E(g,g) ≥ (phi²/2) ∫ g²` —
   `sq_conductance_mul_lintegral_sq_le_lintegral_sub_sq`, using Hölder with `p = q = 2`
   (`ENNReal.lintegral_mul_le_Lp_mul_Lq`) and the `ℝ≥0∞`/Bochner bridge
   `ofReal_two_mul_dirichletFormReal`.
5. Assembling 1–4 over every admissible `f`: `sq_conductance_div_two_le_spectralGap`.

What is new relative to Mathlib v4.32, and reusable independently of Cheeger, is the
co-area section (`lintegral_Ioi_abs_sub_indicator_lt`, `measurable_abs_sub_indicator_lt`,
`lintegral_Ioi_flow_add_flow`), the `L¹` and `L²` isoperimetric inequalities
(`two_mul_conductance_mul_lintegral_le_lintegral_abs_sub`,
`sq_conductance_mul_lintegral_sq_le_lintegral_sub_sq`), and `exists_median`. -/

/-- **`Var f ≤ ∫ (f − c)²` for every constant `c`.**  Immediate from Mathlib
(`variance_sub_const` plus `variance_le_expectation_sq`), and the first step of the hard
direction of Cheeger, where `c` is a median of `f`.

Note this is a statement about variance alone: it says nothing about any Markov chain. -/
theorem varianceReal_le_integral_sub_sq {pi : Measure Ω} [IsProbabilityMeasure pi] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f pi) (c : ℝ) :
    varianceReal pi f ≤ ∫ x, (f x - c) ^ 2 ∂pi := by
  have h1 : varianceReal pi f = ProbabilityTheory.variance (fun x => f x - c) pi :=
    (ProbabilityTheory.variance_sub_const hf c).symm
  have h2 := ProbabilityTheory.variance_le_expectation_sq (μ := pi)
    (hf.sub (aestronglyMeasurable_const (b := c)))
  simpa [Pi.pow_apply] using h1 ▸ h2

/-- **The squared increment dominates the sum of the squared increments of the positive and
negative parts**: `(g x − g y)² + (h x − h y)² ≤ (a − b)²` where `g = ·⁺`, `h = ·⁻`.

Pure arithmetic on `ℝ`, by cases on the signs of `a` and `b`.  Integrating it against
`P x ∂pi` is the second step of the hard direction of Cheeger — the step that lets the
one-sided estimate be applied to the two halves of `f` separately. -/
theorem sq_posPart_sub_add_sq_negPart_sub_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤ (a - b) ^ 2 := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [max_eq_left ha, max_eq_left hb, max_eq_right (by linarith : -a ≤ 0),
      max_eq_right (by linarith : -b ≤ 0)]
    simp
  · rw [max_eq_left ha, max_eq_right hb, max_eq_right (by linarith : -a ≤ 0),
      max_eq_left (by linarith : 0 ≤ -b)]
    nlinarith
  · rw [max_eq_right ha, max_eq_left hb, max_eq_left (by linarith : 0 ≤ -a),
      max_eq_right (by linarith : -b ≤ 0)]
    nlinarith
  · rw [max_eq_right ha, max_eq_right hb, max_eq_left (by linarith : 0 ≤ -a),
      max_eq_left (by linarith : 0 ≤ -b)]
    ring_nf
    simp

/-! ## The co-area formula

The step-3 obstruction described above.  The three lemmas of this section build it from the
bottom up:

1. `lintegral_Ioi_abs_sub_indicator_lt` — the pure one-dimensional fact.  The two half-line
   indicators `t ↦ 1_{t < a}` and `t ↦ 1_{t < b}` disagree exactly on the interval between
   `a` and `b`, so their `L¹(0,∞)` distance is `|a − b|`.  No measure theory on `Ω`.
2. `measurable_abs_sub_indicator_lt` — joint measurability of
   `(t, x, y) ↦ |1_{t < g x} − 1_{t < g y}|` on `ℝ × (Ω × Ω)`, which is what licenses the
   Tonelli exchange.
3. `lintegral_Ioi_flow_add_flow` — the co-area identity itself.

Nothing here mentions `spectralGap` or `conductance`; these are statements about a
nonnegative measurable `g` and the flows across its level sets. -/

/-- **The one-dimensional layer-cake identity, ordered case.**  For `0 ≤ a ≤ b` the half-line
indicators `t ↦ 1_{t < a}` and `t ↦ 1_{t < b}` differ exactly on `[a, b)`, an interval that
lies in `(0, ∞)` up to the single point `a`; so the integral of `|1_{t<a} − 1_{t<b}|` over
`(0, ∞)` is `b − a`. -/
theorem lintegral_Ioi_abs_sub_indicator_lt_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal |(if t < a then (1 : ℝ) else 0) - (if t < b then (1 : ℝ) else 0)|
      = ENNReal.ofReal (b - a) := by
  have hfun : (fun t : ℝ =>
      ENNReal.ofReal |(if t < a then (1 : ℝ) else 0) - (if t < b then (1 : ℝ) else 0)|)
      = Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ≥0∞)) := by
    funext t
    by_cases h1 : t < a
    · have h2 : t < b := lt_of_lt_of_le h1 hab
      simp [h1, h2]
    · rw [not_lt] at h1
      by_cases h2 : t < b
      · have : t ∈ Set.Ico a b := ⟨h1, h2⟩
        simp [not_lt.2 h1, h2, Set.indicator_of_mem this]
      · simp [not_lt.2 h1, h2]
  rw [hfun, lintegral_indicator measurableSet_Ico, setLIntegral_one,
    Measure.restrict_apply measurableSet_Ico]
  refine le_antisymm ?_ ?_
  · exact le_of_le_of_eq (measure_mono Set.inter_subset_left) Real.volume_Ico
  · refine le_of_eq_of_le Real.volume_Ioo.symm (measure_mono ?_)
    exact fun t ht => ⟨⟨ht.1.le, ht.2⟩, lt_of_le_of_lt ha ht.1⟩

/-- **The one-dimensional layer-cake identity.**  For `a, b ≥ 0`,

`∫_{(0,∞)} |1_{t < a} − 1_{t < b}| dt = |a − b|`.

This is the heart of the co-area formula: applied at `a = g x`, `b = g y` it converts an
integral over the levels `t` of `g` into the increment `|g x − g y|`.  Both hypotheses are
needed — the identity fails for `a < 0` because the disagreement interval then sticks out of
`(0, ∞)`. -/
theorem lintegral_Ioi_abs_sub_indicator_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal |(if t < a then (1 : ℝ) else 0) - (if t < b then (1 : ℝ) else 0)|
      = ENNReal.ofReal |a - b| := by
  rcases le_total a b with h | h
  · rw [lintegral_Ioi_abs_sub_indicator_lt_of_le ha h,
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    ring_nf
  · have key := lintegral_Ioi_abs_sub_indicator_lt_of_le hb h
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b), ← key]
    exact lintegral_congr fun t => by rw [abs_sub_comm]

/-- **The level set `{x | t < g x}` is measurable**, and jointly so in `(t, x)`: the set
`{(t, x) | t < g x} ⊆ ℝ × Ω` is measurable.  This is what makes the co-area integrand a
measurable function of the pair, rather than merely of `x` for each fixed `t`. -/
theorem measurableSet_lt_comp {g : Ω → ℝ} (hg : Measurable g) :
    MeasurableSet {q : ℝ × Ω | q.1 < g q.2} :=
  measurableSet_lt measurable_fst (hg.comp measurable_snd)

/-- **Joint measurability of the co-area integrand.**  The function

`(t, x, y) ↦ |1_{t < g x} − 1_{t < g y}|`

is measurable on `ℝ × (Ω × Ω)`.  Each of the two indicators is the indicator of the
measurable set `{(t, p) | t < g p.i}` (`measurableSet_lt_comp` composed with a projection),
so the difference, its absolute value and its `ENNReal.ofReal` all are.

This is ingredient (a) of the co-area formula: it is exactly what licenses the Tonelli
exchange between the level variable `t` and the pair `(x, y)`. -/
theorem measurable_abs_sub_indicator_lt {g : Ω → ℝ} (hg : Measurable g) :
    Measurable (fun q : ℝ × (Ω × Ω) => ENNReal.ofReal
      |(if q.1 < g q.2.1 then (1 : ℝ) else 0) - (if q.1 < g q.2.2 then (1 : ℝ) else 0)|) := by
  have h1 : MeasurableSet {q : ℝ × (Ω × Ω) | q.1 < g q.2.1} :=
    measurableSet_lt measurable_fst (hg.comp (measurable_fst.comp measurable_snd))
  have h2 : MeasurableSet {q : ℝ × (Ω × Ω) | q.1 < g q.2.2} :=
    measurableSet_lt measurable_fst (hg.comp (measurable_snd.comp measurable_snd))
  have m1 : Measurable fun q : ℝ × (Ω × Ω) => (if q.1 < g q.2.1 then (1 : ℝ) else 0) :=
    Measurable.ite h1 measurable_const measurable_const
  have m2 : Measurable fun q : ℝ × (Ω × Ω) => (if q.1 < g q.2.2 then (1 : ℝ) else 0) :=
    Measurable.ite h2 measurable_const measurable_const
  have m3 : Measurable fun q : ℝ × (Ω × Ω) =>
      (if q.1 < g q.2.1 then (1 : ℝ) else 0) - (if q.1 < g q.2.2 then (1 : ℝ) else 0) :=
    m1.sub m2
  have m4 : Measurable fun q : ℝ × (Ω × Ω) =>
      |(if q.1 < g q.2.1 then (1 : ℝ) else 0) - (if q.1 < g q.2.2 then (1 : ℝ) else 0)| :=
    _root_.continuous_abs.measurable.comp m3
  exact m4.ennreal_ofReal

/-- **The two-sided flow across a set is a `compProd` integral.**  For a measurable `S`,

`flow S Sᶜ + flow Sᶜ S = ∫ |1_S(x) − 1_S(y)| d(pi ⊗ₘ P)(x, y)`,

because `(x, y) ↦ |1_S x − 1_S y|` is the indicator of `(S × Sᶜ) ∪ (Sᶜ × S)`, and
`Measure.compProd_apply_prod` reads the measure of a rectangle as a flow. -/
theorem flow_add_flow_compl_eq_lintegral_compProd (P : Kernel Ω Ω) [IsMarkovKernel P]
    (pi : Measure Ω) [IsProbabilityMeasure pi] {S : Set Ω} (hS : MeasurableSet S) :
    flow P pi S Sᶜ + flow P pi Sᶜ S
      = ∫⁻ p, ENNReal.ofReal |Set.indicator S (fun _ => (1 : ℝ)) p.1
          - Set.indicator S (fun _ => (1 : ℝ)) p.2| ∂(pi ⊗ₘ P) := by
  have hsplit : (fun p : Ω × Ω => ENNReal.ofReal |Set.indicator S (fun _ => (1 : ℝ)) p.1
        - Set.indicator S (fun _ => (1 : ℝ)) p.2|)
      = fun p : Ω × Ω => Set.indicator (S ×ˢ Sᶜ) (fun _ => (1 : ℝ≥0∞)) p
        + Set.indicator (Sᶜ ×ˢ S) (fun _ => (1 : ℝ≥0∞)) p := by
    funext p
    by_cases h1 : p.1 ∈ S <;> by_cases h2 : p.2 ∈ S <;>
      simp [h1, h2, Set.mem_prod]
  rw [hsplit, lintegral_add_left (measurable_const.indicator (hS.prod hS.compl)),
    lintegral_indicator (hS.prod hS.compl), setLIntegral_one,
    lintegral_indicator (hS.compl.prod hS), setLIntegral_one,
    Measure.compProd_apply_prod hS hS.compl, Measure.compProd_apply_prod hS.compl hS]
  rfl

/-- **The co-area formula.**  For a measurable `g ≥ 0`, integrating the two-sided flow across
the level set `S_t = {x | t < g x}` over all levels `t > 0` recovers the mean absolute
increment of `g` under one step of the chain:

`∫_0^∞ (flow S_t S_tᶜ + flow S_tᶜ S_t) dt = ∫ |g x − g y| d(pi ⊗ₘ P)(x, y)`.

This is the identity the hard direction of Cheeger turns on, and it is the piece Mathlib
v4.32 does not have: the layer cake `lintegral_comp_eq_lintegral_meas_lt` handles a single
function of one variable, whereas here the level variable must be exchanged with a
*two*-variable integral against a composition-product measure.

The proof is three moves.  `flow_add_flow_compl_eq_lintegral_compProd` turns each level's
flow into a `pi ⊗ₘ P`-integral; `measurable_abs_sub_indicator_lt` gives joint measurability
on `ℝ × (Ω × Ω)`, so `lintegral_lintegral_swap` may exchange `t` with `(x, y)` (both
`volume.restrict (Ioi 0)` and `pi ⊗ₘ P` are `SFinite`); and the inner one-dimensional
integral is `lintegral_Ioi_abs_sub_indicator_lt`, which is where `g ≥ 0` is used.

Note this is an *identity*, not an estimate: no reversibility, no conductance, nothing about
the spectral gap. -/
theorem lintegral_Ioi_flow_add_flow (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    [IsProbabilityMeasure pi] {g : Ω → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        (flow P pi {x | t < g x} {x | t < g x}ᶜ + flow P pi {x | t < g x}ᶜ {x | t < g x})
      = ∫⁻ p, ENNReal.ofReal |g p.1 - g p.2| ∂(pi ⊗ₘ P) := by
  have hFmeas : Measurable (Function.uncurry fun (t : ℝ) (p : Ω × Ω) => ENNReal.ofReal
      |(if t < g p.1 then (1 : ℝ) else 0) - (if t < g p.2 then (1 : ℝ) else 0)|) :=
    measurable_abs_sub_indicator_lt hg
  have hA : ∀ t : ℝ, flow P pi {x | t < g x} {x | t < g x}ᶜ
        + flow P pi {x | t < g x}ᶜ {x | t < g x}
      = ∫⁻ p, ENNReal.ofReal
          |(if t < g p.1 then (1 : ℝ) else 0) - (if t < g p.2 then (1 : ℝ) else 0)|
          ∂(pi ⊗ₘ P) := by
    intro t
    have hS : MeasurableSet {x : Ω | t < g x} := measurableSet_lt measurable_const hg
    rw [flow_add_flow_compl_eq_lintegral_compProd P pi hS]
    refine lintegral_congr fun p => ?_
    by_cases h1 : t < g p.1 <;> by_cases h2 : t < g p.2 <;>
      simp [Set.mem_setOf_eq, h1, h2]
  simp_rw [hA]
  rw [lintegral_lintegral_swap hFmeas.aemeasurable]
  exact lintegral_congr fun p => lintegral_Ioi_abs_sub_indicator_lt (hg0 p.1) (hg0 p.2)

/-- **The conductance bounds every small set's escape flow from below**:
`Φ · pi(S) ≤ flow(S, Sᶜ)` whenever `pi S ≤ 1/2`.

This is `conductance_le_conductanceOn` cleared of its denominator by
`flow_eq_conductanceOn_mul`.  The `pi S = 0` case needs no positivity hypothesis because
`Φ · 0 = 0` in `ℝ≥0∞` even for `Φ = ⊤`. -/
theorem conductance_mul_measure_le_flow (P : Kernel Ω Ω) (pi : Measure Ω)
    [IsProbabilityMeasure pi] {S : Set Ω} (hS : MeasurableSet S) (hhalf : pi S ≤ 1 / 2) :
    conductance P pi * pi S ≤ flow P pi S Sᶜ := by
  rcases eq_zero_or_pos (pi S) with h | h
  · simp [h]
  · rw [← flow_eq_conductanceOn_mul P pi h (measure_ne_top pi S)]
    gcongr
    exact conductance_le_conductanceOn P pi hS h hhalf

/-- **The `L¹` isoperimetric inequality for a reversible chain.**  For a measurable `g ≥ 0`
whose support has `pi`-measure at most `1/2`,

`2 Φ ∫ g dpi ≤ ∫ |g x − g y| d(pi ⊗ₘ P)(x, y)`.

Every level set `S_t = {x | t < g x}` with `t > 0` sits inside `{g > 0}` and so is small
enough for the conductance bound `Φ · pi(S_t) ≤ flow(S_t, S_tᶜ)`
(`conductance_mul_measure_le_flow`); detailed balance makes the reverse flow equal to the
forward one, doubling the constant.  Integrating over `t` and applying the layer cake
`lintegral_eq_lintegral_meas_lt` on the left and the co-area formula
`lintegral_Ioi_flow_add_flow` on the right gives the claim.

Everything is in `ℝ≥0∞`: no integrability hypothesis on `g` is needed, and the statement is
true (both sides `⊤`) when `g` is not integrable.

This is *not* the Cheeger inequality: it bounds an `L¹` quantity, and the `L²` statement
`Φ²/2 ≤ gap` needs it applied to `g²` together with Cauchy–Schwarz — see the closing note. -/
theorem two_mul_conductance_mul_lintegral_le_lintegral_abs_sub {P : Kernel Ω Ω}
    [IsMarkovKernel P] {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {g : Ω → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hsupp : pi {x | 0 < g x} ≤ 1 / 2) :
    2 * conductance P pi * ∫⁻ x, ENNReal.ofReal (g x) ∂pi
      ≤ ∫⁻ p, ENNReal.ofReal |g p.1 - g p.2| ∂(pi ⊗ₘ P) := by
  rw [← lintegral_Ioi_flow_add_flow P pi hg hg0,
    lintegral_eq_lintegral_meas_lt pi (Filter.Eventually.of_forall hg0) hg.aemeasurable]
  refine le_trans (lintegral_const_mul_le _ _) (lintegral_mono_ae ?_)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have hS : MeasurableSet {x : Ω | t < g x} := measurableSet_lt measurable_const hg
  have hsub : {x : Ω | t < g x} ⊆ {x : Ω | 0 < g x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact lt_trans ht hx
  have hhalf : pi {x : Ω | t < g x} ≤ 1 / 2 := le_trans (measure_mono hsub) hsupp
  have hflow := conductance_mul_measure_le_flow P pi hS hhalf
  rw [hrev {x : Ω | t < g x}ᶜ {x : Ω | t < g x} hS.compl hS]
  calc 2 * conductance P pi * pi {x : Ω | t < g x}
      = conductance P pi * pi {x : Ω | t < g x}
        + conductance P pi * pi {x : Ω | t < g x} := by ring
    _ ≤ _ := add_le_add hflow hflow

/-! ### A non-vacuity witness for the `L¹` isoperimetric inequality (`CLAUDE.md` §11)

`two_mul_conductance_mul_lintegral_le_lintegral_abs_sub` is a `∀`-statement, so it would be
worthless if its hypotheses were unsatisfiable, or if both sides were `0` (or both `⊤`) on
every chain that satisfies them.  On `Kernel.const Bool piHalf` with `g = 1_{true}` all the
hypotheses hold and **both sides are exactly `1/2`**: the inequality is attained. -/

/-- The Lebesgue integral against `piHalf` is the average of the two values. -/
theorem lintegral_piHalf (F : Bool → ℝ≥0∞) : ∫⁻ b, F b ∂piHalf = 1 / 2 * (F true + F false) := by
  rw [piHalf, lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, lintegral_dirac,
    smul_eq_mul]

/-- The left side of the `L¹` isoperimetric inequality at the `Bool` witness: `2 · (1/2) · (1/2)`. -/
theorem lintegral_ofReal_indicator_piHalf :
    ∫⁻ x, ENNReal.ofReal (Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)) x) ∂piHalf
      = 1 / 2 := by
  rw [lintegral_piHalf]
  norm_num

/-- The right side of the `L¹` isoperimetric inequality at the `Bool` witness: one step of the
instantly mixing chain changes `1_{true}` with probability exactly `1/2`. -/
theorem lintegral_abs_sub_indicator_compProd_piHalf :
    ∫⁻ p, ENNReal.ofReal |Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)) p.1
        - Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)) p.2|
      ∂(piHalf ⊗ₘ Kernel.const Bool piHalf) = 1 / 2 := by
  have hgm : Measurable (Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (measurableSet_singleton true)
  have hm : Measurable fun p : Bool × Bool =>
      ENNReal.ofReal |Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)) p.1
        - Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)) p.2| :=
    (_root_.continuous_abs.measurable.comp
      ((hgm.comp measurable_fst).sub (hgm.comp measurable_snd))).ennreal_ofReal
  rw [Measure.lintegral_compProd hm]
  simp only [Kernel.const_apply]
  rw [lintegral_piHalf]
  rw [lintegral_piHalf, lintegral_piHalf]
  norm_num
  rw [ENNReal.inv_two_add_inv_two, mul_one]

/-- **The `L¹` isoperimetric inequality is attained, hence not vacuous** (`CLAUDE.md` §11).
On `Kernel.const Bool piHalf` with `g = 1_{true}` — a reversible chain, a nonnegative
measurable `g`, and `pi {g > 0} = 1/2` — both sides of
`two_mul_conductance_mul_lintegral_le_lintegral_abs_sub` equal `1/2`.

So the inequality relates two quantities that are simultaneously finite and nonzero on a
concrete chain, and its constant `2 Φ` cannot be improved. -/
theorem two_mul_conductance_mul_lintegral_eq_lintegral_abs_sub_piHalf :
    2 * conductance (Kernel.const Bool piHalf) piHalf
        * ∫⁻ x, ENNReal.ofReal (Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)) x) ∂piHalf
      = ∫⁻ p, ENNReal.ofReal |Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)) p.1
          - Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)) p.2|
        ∂(piHalf ⊗ₘ Kernel.const Bool piHalf) := by
  rw [conductance_const_piHalf, lintegral_ofReal_indicator_piHalf,
    lintegral_abs_sub_indicator_compProd_piHalf]
  rw [ENNReal.mul_div_cancel' (by norm_num) (by norm_num), one_mul]

/-- The hypotheses of `two_mul_conductance_mul_lintegral_le_lintegral_abs_sub` are
satisfiable, with both sides positive and finite. -/
theorem exists_isoperimetric_witness :
    ∃ (Om : Type) (_ : MeasurableSpace Om) (P : Kernel Om Om) (pi : Measure Om) (g : Om → ℝ),
      ∃ (_ : IsMarkovKernel P) (_ : IsProbabilityMeasure pi), IsReversible P pi ∧
        Measurable g ∧ (∀ x, 0 ≤ g x) ∧ pi {x | 0 < g x} ≤ 1 / 2 ∧
        2 * conductance P pi * ∫⁻ x, ENNReal.ofReal (g x) ∂pi = 1 / 2 ∧
        ∫⁻ p, ENNReal.ofReal |g p.1 - g p.2| ∂(pi ⊗ₘ P) = 1 / 2 := by
  refine ⟨Bool, inferInstance, Kernel.const Bool piHalf, piHalf,
    Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)), inferInstance, inferInstance,
    isReversible_const piHalf, measurable_const.indicator (measurableSet_singleton true),
    fun x => Set.indicator_apply_nonneg fun _ => zero_le_one, ?_, ?_,
    lintegral_abs_sub_indicator_compProd_piHalf⟩
  · have hset : {x : Bool | 0 < Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)) x}
        = ({true} : Set Bool) := by
      ext x; cases x <;> simp
    rw [hset, piHalf_singleton]
  · rw [conductance_const_piHalf, lintegral_ofReal_indicator_piHalf,
      ENNReal.mul_div_cancel' (by norm_num) (by norm_num), one_mul]

/-! ## Medians

Mathlib v4.32 has no median of a real random variable.  The one fact the hard direction of
Cheeger needs is existence of a level that splits the mass evenly, which is proved here from
scratch as `sInf {t | pi {f ≤ t} ≥ 1/2}` together with right-continuity of the CDF (which is
continuity from above of `pi` along `{f ≤ m + 1/n}`). -/

/-- **Existence of a median.**  Every real measurable `f` on a probability space admits a
level `m` with

`pi {x | m < f x} ≤ 1/2` and `pi {x | f x < m} ≤ 1/2`.

Take `m = sInf B` with `B = {t | 1/2 ≤ pi {f ≤ t}}`.  `B` is an up-set, nonempty (the
measures `pi {f ≤ n}` increase to `1`) and bounded below (the measures `pi {f ≤ −n}` decrease
to `0`).  Right-continuity — `pi {f ≤ m} = lim_n pi {f ≤ m + 1/(n+1)}` by continuity from
above — puts `m` itself in `B`, which gives the first bound; and no `t < m` lies in `B`,
which after continuity from below along `{f ≤ m − 1/(n+1)}` gives the second.

Both inequalities are `≤ 1/2`; the usual `pi {f ≥ m} ≥ 1/2` is the complement of the first.
This is exactly the splitting the hard direction of Cheeger uses to cut `f` into a positive
and a negative part, each supported on a set of measure at most `1/2`. -/
theorem exists_median {pi : Measure Ω} [IsProbabilityMeasure pi] {f : Ω → ℝ}
    (hf : Measurable f) :
    ∃ m : ℝ, pi {x | m < f x} ≤ 1 / 2 ∧ pi {x | f x < m} ≤ 1 / 2 := by
  have hle : ∀ t : ℝ, MeasurableSet {x : Ω | f x ≤ t} := fun t =>
    measurableSet_le hf measurable_const
  have hmono : ∀ s t : ℝ, s ≤ t → pi {x : Ω | f x ≤ s} ≤ pi {x : Ω | f x ≤ t} := fun s t hst =>
    measure_mono fun x hx => le_trans hx hst
  set B : Set ℝ := {t : ℝ | 1 / 2 ≤ pi {x : Ω | f x ≤ t}} with hBdef
  have hup : ∀ s ∈ B, ∀ t : ℝ, s ≤ t → t ∈ B := fun s hs t hst => le_trans hs (hmono s t hst)
  -- `B` is nonempty: `pi {f ≤ n} → 1`.
  have hne : B.Nonempty := by
    have hU : (⋃ n : ℕ, {x : Ω | f x ≤ (n : ℝ)}) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact exists_nat_ge (f x)
    have hm : Monotone fun n : ℕ => {x : Ω | f x ≤ (n : ℝ)} := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact le_trans hx (by exact_mod_cast hab)
    have h := tendsto_measure_iUnion_atTop (μ := pi) hm
    rw [hU, measure_univ] at h
    obtain ⟨n, hn⟩ := (h.eventually_const_lt (by norm_num : (1 : ℝ≥0∞) / 2 < 1)).exists
    exact ⟨(n : ℝ), hn.le⟩
  -- `B` is bounded below: `pi {f ≤ −n} → 0`.
  have hbdd : BddBelow B := by
    have hI : (⋂ n : ℕ, {x : Ω | f x ≤ -(n : ℝ)}) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-(f x))
      exact ⟨n, by linarith⟩
    have hm : Antitone fun n : ℕ => {x : Ω | f x ≤ -(n : ℝ)} := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    have h := tendsto_measure_iInter_atTop (μ := pi)
      (fun n : ℕ => (hle (-(n : ℝ))).nullMeasurableSet) hm ⟨0, measure_ne_top pi _⟩
    rw [hI, measure_empty] at h
    obtain ⟨n, hn⟩ := (h.eventually_lt_const (by norm_num : (0 : ℝ≥0∞) < 1 / 2)).exists
    refine ⟨-(n : ℝ), fun t ht => ?_⟩
    by_contra hlt
    exact absurd (le_trans ht (hmono t (-(n : ℝ)) (not_le.1 hlt).le)) (not_le.2 hn)
  set m : ℝ := sInf B with hmdef
  -- Right-continuity puts `m` itself in `B`.
  have hmB : (1 : ℝ≥0∞) / 2 ≤ pi {x : Ω | f x ≤ m} := by
    have hI : (⋂ n : ℕ, {x : Ω | f x ≤ m + 1 / (n + 1 : ℝ)}) = {x : Ω | f x ≤ m} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h => le_of_forall_pos_le_add fun ε hε => ?_, fun h n => ?_⟩
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        exact le_trans (h n) (by linarith)
      · have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        linarith
    have hm : Antitone fun n : ℕ => {x : Ω | f x ≤ m + 1 / (n + 1 : ℝ)} := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have hab' : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        linarith
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hab'
      linarith
    have h := tendsto_measure_iInter_atTop (μ := pi)
      (fun n : ℕ => (hle (m + 1 / (n + 1 : ℝ))).nullMeasurableSet) hm ⟨0, measure_ne_top pi _⟩
    rw [hI] at h
    refine ge_of_tendsto h (Filter.Eventually.of_forall fun n => ?_)
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    obtain ⟨s, hsB, hs⟩ := exists_lt_of_csInf_lt hne (by linarith : sInf B < m + 1 / (n + 1 : ℝ))
    exact hup s hsB _ hs.le
  refine ⟨m, ?_, ?_⟩
  · -- `pi {m < f}` is the complement of `pi {f ≤ m} ≥ 1/2`.
    have hcompl : {x : Ω | m < f x} = {x : Ω | f x ≤ m}ᶜ := by
      ext x; simp [not_le]
    have hsum : pi {x : Ω | f x ≤ m} + pi {x : Ω | f x ≤ m}ᶜ = 1 := by
      rw [measure_add_measure_compl (hle m)]; exact measure_univ
    by_contra hgt
    rw [hcompl] at hgt
    have h1 : pi {x : Ω | f x ≤ m} + 1 / 2
        < pi {x : Ω | f x ≤ m} + pi {x : Ω | f x ≤ m}ᶜ :=
      ENNReal.add_lt_add_left (measure_ne_top pi _) (not_le.1 hgt)
    rw [hsum] at h1
    refine absurd h1 (not_lt.2 ?_)
    calc (1 : ℝ≥0∞) = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
      _ ≤ _ := add_le_add hmB le_rfl
  · -- No `t < m` lies in `B`, and `{f < m} = ⋃ n, {f ≤ m − 1/(n+1)}`.
    have hU : (⋃ n : ℕ, {x : Ω | f x ≤ m - 1 / (n + 1 : ℝ)}) = {x : Ω | f x < m} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        linarith
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < m - f x)
        exact ⟨n, by linarith⟩
    have hm : Monotone fun n : ℕ => {x : Ω | f x ≤ m - 1 / (n + 1 : ℝ)} := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have hab' : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        linarith
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hab'
      linarith
    have h := tendsto_measure_iUnion_atTop (μ := pi) hm
    rw [hU] at h
    refine le_of_tendsto h (Filter.Eventually.of_forall fun n => ?_)
    by_contra hgt
    have hmem : m ≤ m - 1 / (n + 1 : ℝ) := csInf_le hbdd (not_le.1 hgt).le
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith

/-! ## The `L²` bridge: the Bochner Dirichlet form as an `ℝ≥0∞` double integral

The `L¹` isoperimetric inequality above lives entirely in `ℝ≥0∞`, over the measure
`pi ⊗ₘ P`; `dirichletFormReal` is a Bochner *iterated* integral over `ℝ`.  The two are the
same number, but saying so requires (a) Fubini for the composition product
(`MeasureTheory.Measure.integral_compProd`) to collapse the iterated integral, and (b)
`ofReal_integral_eq_lintegral_ofReal` to move a nonnegative Bochner integral into `ℝ≥0∞`.
Both need genuine integrability of `(x, y) ↦ (g x − g y)²`, which is therefore an explicit
hypothesis. -/

/-- **The `L²`/Bochner bridge.**  For an integrable squared increment,

`ofReal (2 · E(g,g)) = ∫⁻ (g x − g y)² d(pi ⊗ₘ P)(x, y)`.

The factor `2` is the one in the definition of `dirichletFormReal`; putting it on the left
avoids dividing in `ℝ≥0∞`.

The integrability hypothesis cannot be dropped: without it the Bochner iterated integral
defining `dirichletFormReal` is the junk value `0` while the right side can be `⊤`.  It is
*not* implied by `MemLp g 2 pi` alone — see `integrable_sq_sub_compProd` below, which
derives it from `MemLp g 2 pi` plus measurability plus invariance of `pi`. -/
theorem ofReal_two_mul_dirichletFormReal (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    [IsProbabilityMeasure pi] {g : Ω → ℝ}
    (hint : Integrable (fun p : Ω × Ω => (g p.1 - g p.2) ^ 2) (pi ⊗ₘ P)) :
    ENNReal.ofReal (2 * dirichletFormReal P pi g)
      = ∫⁻ p, ENNReal.ofReal ((g p.1 - g p.2) ^ 2) ∂(pi ⊗ₘ P) := by
  have h2 : 2 * dirichletFormReal P pi g = ∫ p, (g p.1 - g p.2) ^ 2 ∂(pi ⊗ₘ P) := by
    rw [Measure.integral_compProd hint, dirichletFormReal]
    ring
  rw [h2]
  exact ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-! ### The two marginals of `pi ⊗ₘ P`

`pi ⊗ₘ P` has first marginal `pi` because `P` is Markov, and second marginal `pi` because
`pi` is invariant.  Only the second is a real hypothesis; it is the single place the hard
direction uses stationarity rather than detailed balance. -/

/-- **The first marginal of `pi ⊗ₘ P` is `pi`**, for a Markov kernel: integrating a function
of the first coordinate only, the inner integral is against a probability measure. -/
theorem lintegral_compProd_fst (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    [IsProbabilityMeasure pi] {F : Ω → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p.1 ∂(pi ⊗ₘ P) = ∫⁻ x, F x ∂pi := by
  have hF1 : Measurable fun p : Ω × Ω => F p.1 := hF.comp measurable_fst
  rw [Measure.lintegral_compProd hF1]
  simp

/-- **The second marginal of `pi ⊗ₘ P` is `pi`**, exactly when `pi` is invariant.  This is
the only use of stationarity in the `L²` step; `IsReversible.invariant` supplies it for a
reversible chain. -/
theorem lintegral_compProd_snd_of_invariant {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {F : Ω → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p, F p.2 ∂(pi ⊗ₘ P) = ∫⁻ x, F x ∂pi := by
  have hF2 : Measurable fun p : Ω × Ω => F p.2 := hF.comp measurable_snd
  have hbind : ∫⁻ x, F x ∂(pi.bind ⇑P) = ∫⁻ a, ∫⁻ x, F x ∂(P a) ∂pi :=
    Measure.lintegral_bind (Kernel.measurable P).aemeasurable hF.aemeasurable
  rw [Measure.lintegral_compProd hF2]
  simpa [hinv.def] using hbind.symm

/-- **The `L²` norm of the sum is at most four times the `L²` norm.**  Pointwise
`(a + b)² ≤ 2a² + 2b²`, and both marginals of `pi ⊗ₘ P` are `pi`, so

`∫⁻ (g x + g y)² d(pi ⊗ₘ P) ≤ 4 ∫⁻ g² dpi`.

This is the "cheap" factor in the Cauchy–Schwarz step; the constant `4` is what turns
`2 Φ` into `Φ` after the square root. -/
theorem lintegral_le_four_mul_of_le {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {g : Ω → ℝ} (hg : Measurable g)
    {F : Ω × Ω → ℝ} (hF : ∀ p, F p ≤ 2 * g p.1 ^ 2 + 2 * g p.2 ^ 2) :
    ∫⁻ p, ENNReal.ofReal (F p) ∂(pi ⊗ₘ P) ≤ 4 * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi := by
  have hsq : Measurable fun x => ENNReal.ofReal (g x ^ 2) := (hg.pow_const 2).ennreal_ofReal
  have hsq1 : Measurable fun p : Ω × Ω => ENNReal.ofReal (g p.1 ^ 2) :=
    hsq.comp measurable_fst
  have hsq2 : Measurable fun p : Ω × Ω => ENNReal.ofReal (g p.2 ^ 2) :=
    hsq.comp measurable_snd
  have hm1 : Measurable fun p : Ω × Ω => 2 * ENNReal.ofReal (g p.1 ^ 2) := hsq1.const_mul 2
  have hpt : ∀ p : Ω × Ω, ENNReal.ofReal (F p)
      ≤ 2 * ENNReal.ofReal (g p.1 ^ 2) + 2 * ENNReal.ofReal (g p.2 ^ 2) := by
    intro p
    calc ENNReal.ofReal (F p)
        ≤ ENNReal.ofReal (2 * g p.1 ^ 2 + 2 * g p.2 ^ 2) := ENNReal.ofReal_le_ofReal (hF p)
      _ = 2 * ENNReal.ofReal (g p.1 ^ 2) + 2 * ENNReal.ofReal (g p.2 ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
  calc ∫⁻ p, ENNReal.ofReal (F p) ∂(pi ⊗ₘ P)
      ≤ ∫⁻ p, (2 * ENNReal.ofReal (g p.1 ^ 2) + 2 * ENNReal.ofReal (g p.2 ^ 2)) ∂(pi ⊗ₘ P) :=
        lintegral_mono hpt
    _ = 2 * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi + 2 * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi := by
        rw [lintegral_add_left hm1, lintegral_const_mul _ hsq1, lintegral_const_mul _ hsq2,
          lintegral_compProd_fst P pi hsq, lintegral_compProd_snd_of_invariant hinv hsq]
    _ = 4 * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi := by ring

/-- The `+` instance of `lintegral_le_four_mul_of_le`, used by the Cauchy–Schwarz step. -/
theorem lintegral_add_sq_le_four_mul {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {g : Ω → ℝ} (hg : Measurable g) :
    ∫⁻ p, ENNReal.ofReal ((g p.1 + g p.2) ^ 2) ∂(pi ⊗ₘ P)
      ≤ 4 * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi :=
  lintegral_le_four_mul_of_le hinv hg fun p => by nlinarith [sq_nonneg (g p.1 - g p.2)]

/-- The `−` instance of `lintegral_le_four_mul_of_le`, used to prove that the squared
increment is `pi ⊗ₘ P`-integrable (`integrable_sq_sub_compProd`). -/
theorem lintegral_sub_sq_le_four_mul {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {g : Ω → ℝ} (hg : Measurable g) :
    ∫⁻ p, ENNReal.ofReal ((g p.1 - g p.2) ^ 2) ∂(pi ⊗ₘ P)
      ≤ 4 * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi :=
  lintegral_le_four_mul_of_le hinv hg fun p => by nlinarith [sq_nonneg (g p.1 + g p.2)]

/-! ### Cauchy–Schwarz: from the `L¹` inequality to the `L²` one

The `L¹` isoperimetric inequality applied to `g²` reads

`2 Φ ∫⁻ g² dpi ≤ ∫⁻ |g(x)² − g(y)²| d(pi ⊗ₘ P)`,

and the right side factors as `∫⁻ |g x − g y| · (g x + g y)`.  Hölder with `p = q = 2`
splits it into `(∫⁻ (g x − g y)²)^{1/2} (∫⁻ (g x + g y)²)^{1/2}`, and
`lintegral_add_sq_le_four_mul` bounds the second factor by `(4 ∫⁻ g²)^{1/2}`.  Cancelling
`∫⁻ g²` — which is where finiteness of the `L²` norm is used — leaves `Φ² ∫⁻ g² ≤ ∫⁻ (g x −
g y)²`, the `L²` isoperimetric inequality.

The `ℝ≥0∞` bookkeeping of that cancellation is isolated in `sq_mul_le_of_two_mul_le`, which
is pure arithmetic in `ℝ≥0∞` and mentions no measure at all. -/

/-- Squaring undoes the square root in `ℝ≥0∞`: `(x^{1/2})² = x`, with no side condition. -/
theorem rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
  norm_num

/-- `4^{1/2} = 2` in `ℝ≥0∞`. -/
theorem rpow_half_four : (4 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 2 := by
  rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℕ) by norm_num, ← ENNReal.rpow_natCast (2 : ℝ≥0∞) 2,
    ← ENNReal.rpow_mul]
  norm_num

/-- **The `ℝ≥0∞` arithmetic behind the Cauchy–Schwarz step.**  If

`2 c A ≤ D^{1/2} S^{1/2}` and `S ≤ 4 A` and `A < ⊤`, then `c² A ≤ D`.

Pure arithmetic: substitute `S^{1/2} ≤ 2 A^{1/2}`, cancel the `2`, cancel one factor of
`A^{1/2}` (legitimate because `A ≠ 0` — the `A = 0` case is trivial — and `A ≠ ⊤`), and
square.  No measure theory, no probability.  `A ≠ ⊤` is essential: for `A = ⊤` the
hypothesis is vacuous while the conclusion can fail. -/
theorem sq_mul_le_of_two_mul_le {c A D S : ℝ≥0∞} (hA : A ≠ ⊤)
    (h : 2 * c * A ≤ D ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ)) (hS : S ≤ 4 * A) :
    c ^ 2 * A ≤ D := by
  rcases eq_or_ne A 0 with h0 | h0
  · simp [h0]
  have hAh0 : A ^ (1 / 2 : ℝ) ≠ 0 := fun hc => h0 (by rw [← rpow_half_sq A, hc]; simp)
  have hAht : A ^ (1 / 2 : ℝ) ≠ ⊤ := fun hc => hA (by rw [← rpow_half_sq A, hc]; simp)
  have hS2 : S ^ (1 / 2 : ℝ) ≤ 2 * A ^ (1 / 2 : ℝ) := by
    calc S ^ (1 / 2 : ℝ) ≤ (4 * A) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hS (by norm_num)
      _ = (4 : ℝ≥0∞) ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = 2 * A ^ (1 / 2 : ℝ) := by rw [rpow_half_four]
  have hstep : 2 * (c * A) ≤ 2 * (D ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)) := by
    calc 2 * (c * A) = 2 * c * A := by ring
      _ ≤ D ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := h
      _ ≤ D ^ (1 / 2 : ℝ) * (2 * A ^ (1 / 2 : ℝ)) := by gcongr
      _ = 2 * (D ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)) := by ring
  have hcancel : c * A ≤ D ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) :=
    (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 hstep
  have hA2 : A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := by rw [← pow_two, rpow_half_sq]
  have hcancel2 : c * A ^ (1 / 2 : ℝ) ≤ D ^ (1 / 2 : ℝ) := by
    refine (ENNReal.mul_le_mul_iff_left hAh0 hAht).1 ?_
    calc c * A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = c * A := by rw [mul_assoc, hA2]
      _ ≤ _ := hcancel
  calc c ^ 2 * A = (c * A ^ (1 / 2 : ℝ)) ^ 2 := by rw [mul_pow, rpow_half_sq]
    _ ≤ (D ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = D := rpow_half_sq D

/-- **The `L²` isoperimetric inequality** — the Cauchy–Schwarz step of Cheeger's hard
direction.  For a reversible chain and a measurable `g ≥ 0` with `pi {g > 0} ≤ 1/2` and
finite `L²` norm,

`Φ² ∫⁻ g² dpi ≤ ∫⁻ (g x − g y)² d(pi ⊗ₘ P)(x, y)`.

Everything is in `ℝ≥0∞`, so the only side condition is `∫⁻ g² dpi ≠ ⊤` — which is genuinely
needed, being what licenses cancelling that factor.

This is still *not* the Cheeger inequality: it is a statement about one nonnegative `g`, not
about the spectral gap, and the passage to the Bochner Dirichlet form is
`ofReal_two_mul_dirichletFormReal`. -/
theorem sq_conductance_mul_lintegral_sq_le_lintegral_sub_sq {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi) {g : Ω → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hsupp : pi {x | 0 < g x} ≤ 1 / 2)
    (hA : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi ≠ ⊤) :
    conductance P pi ^ 2 * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi
      ≤ ∫⁻ p, ENNReal.ofReal ((g p.1 - g p.2) ^ 2) ∂(pi ⊗ₘ P) := by
  -- the support of `g²` is the support of `g`
  have hset : {x : Ω | 0 < g x ^ 2} = {x : Ω | 0 < g x} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hc
      have : g x = 0 := le_antisymm (not_lt.1 hc) (hg0 x)
      simp [this] at h
    · intro h; positivity
  -- the `L¹` inequality applied to `g²`
  have hL1 := two_mul_conductance_mul_lintegral_le_lintegral_abs_sub hrev (hg.pow_const 2)
    (fun x => sq_nonneg _) (by rw [hset]; exact hsupp)
  -- factor `|a² − b²| = |a − b| (a + b)`
  have hfac : ∀ p : Ω × Ω, ENNReal.ofReal |g p.1 ^ 2 - g p.2 ^ 2|
      = ENNReal.ofReal |g p.1 - g p.2| * ENNReal.ofReal (g p.1 + g p.2) := by
    intro p
    have h1 : |g p.1 ^ 2 - g p.2 ^ 2| = |g p.1 - g p.2| * (g p.1 + g p.2) := by
      rw [show g p.1 ^ 2 - g p.2 ^ 2 = (g p.1 - g p.2) * (g p.1 + g p.2) by ring, abs_mul,
        abs_of_nonneg (add_nonneg (hg0 _) (hg0 _))]
    rw [h1, ENNReal.ofReal_mul (abs_nonneg _)]
  -- Hölder with `p = q = 2`
  have hm1 : Measurable fun p : Ω × Ω => ENNReal.ofReal |g p.1 - g p.2| :=
    (_root_.continuous_abs.measurable.comp
      ((hg.comp measurable_fst).sub (hg.comp measurable_snd))).ennreal_ofReal
  have hm2 : Measurable fun p : Ω × Ω => ENNReal.ofReal (g p.1 + g p.2) :=
    ((hg.comp measurable_fst).add (hg.comp measurable_snd)).ennreal_ofReal
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (pi ⊗ₘ P) Real.HolderConjugate.two_two
    hm1.aemeasurable hm2.aemeasurable
  simp only [Pi.mul_apply] at hCS
  have hpow1 : ∀ p : Ω × Ω, (ENNReal.ofReal |g p.1 - g p.2|) ^ (2 : ℝ)
      = ENNReal.ofReal ((g p.1 - g p.2) ^ 2) := by
    intro p
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hpow2 : ∀ p : Ω × Ω, (ENNReal.ofReal (g p.1 + g p.2)) ^ (2 : ℝ)
      = ENNReal.ofReal ((g p.1 + g p.2) ^ 2) := by
    intro p
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (add_nonneg (hg0 _) (hg0 _))]
  simp only [hpow1, hpow2] at hCS
  -- assemble
  refine sq_mul_le_of_two_mul_le hA ?_ (lintegral_add_sq_le_four_mul hrev.invariant hg)
  calc 2 * conductance P pi * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi
      ≤ ∫⁻ p, ENNReal.ofReal |g p.1 ^ 2 - g p.2 ^ 2| ∂(pi ⊗ₘ P) := hL1
    _ = ∫⁻ p, ENNReal.ofReal |g p.1 - g p.2| * ENNReal.ofReal (g p.1 + g p.2) ∂(pi ⊗ₘ P) :=
        lintegral_congr hfac
    _ ≤ _ := hCS

/-! ### Discharging the integrability side condition

`ofReal_two_mul_dirichletFormReal` takes `Integrable (fun p => (g p.1 − g p.2)²) (pi ⊗ₘ P)`
as a hypothesis.  For a measurable `g ∈ L²(pi)` on an invariant `pi` it is not an extra
assumption at all: `(a − b)² ≤ 2a² + 2b²`, and both marginals of `pi ⊗ₘ P` are `pi`. -/

/-- `∫⁻ g² dpi` is finite for `g ∈ L²(pi)`. -/
theorem lintegral_sq_ne_top_of_memLp {pi : Measure Ω} [IsProbabilityMeasure pi] {g : Ω → ℝ}
    (hmem : MemLp g 2 pi) : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂pi ≠ ⊤ :=
  ((hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => sq_nonneg (g x))).1
      hmem.integrable_sq.hasFiniteIntegral).ne

/-- **The squared increment is `pi ⊗ₘ P`-integrable** for a measurable `g ∈ L²(pi)` and an
invariant `pi`.  This is the hypothesis of `ofReal_two_mul_dirichletFormReal`, discharged. -/
theorem integrable_sq_sub_compProd {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {g : Ω → ℝ} (hg : Measurable g)
    (hmem : MemLp g 2 pi) :
    Integrable (fun p : Ω × Ω => (g p.1 - g p.2) ^ 2) (pi ⊗ₘ P) := by
  refine ⟨(((hg.comp measurable_fst).sub (hg.comp measurable_snd)).pow_const
    2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => sq_nonneg _)]
  refine lt_of_le_of_lt (lintegral_sub_sq_le_four_mul hinv hg) ?_
  exact ENNReal.mul_lt_top (by norm_num) (lintegral_sq_ne_top_of_memLp hmem).lt_top

/-! ### Splitting a function into its positive and negative parts

Step 2 of the hard direction: the Dirichlet energy of `f` dominates the sum of the energies
of `f⁺` and `f⁻`.  The pointwise inequality is `sq_posPart_sub_add_sq_negPart_sub_le`; the
integration is done in `ℝ≥0∞`, where `lintegral_mono` needs no side condition, and moved
back to `ℝ` through `ofReal_two_mul_dirichletFormReal` at the very end. -/

/-- `f⁺` and `f⁻` are measurable and in `L²` whenever `f` is. -/
theorem memLp_two_max_zero {pi : Measure Ω} {f : Ω → ℝ} (hf : Measurable f)
    (hmem : MemLp f 2 pi) : MemLp (fun x => max (f x) 0) 2 pi :=
  hmem.of_le (hf.max measurable_const).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rcases le_total 0 (f x) with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h, abs_zero]; exact abs_nonneg _)

/-- **The energy splits over positive and negative parts**:

`E(f⁺, f⁺) + E(f⁻, f⁻) ≤ E(f, f)`.

`sq_posPart_sub_add_sq_negPart_sub_le` gives this pointwise on increments; the rest is
`lintegral_mono` in `ℝ≥0∞` plus three applications of the `L²` bridge.  The `MemLp`
hypothesis is what makes all three bridges available (`integrable_sq_sub_compProd`). -/
theorem dirichletFormReal_posPart_add_negPart_le {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {f : Ω → ℝ}
    (hf : Measurable f) (hmem : MemLp f 2 pi) :
    dirichletFormReal P pi (fun x => max (f x) 0)
        + dirichletFormReal P pi (fun x => max (-(f x)) 0)
      ≤ dirichletFormReal P pi f := by
  set g : Ω → ℝ := fun x => max (f x) 0 with hgdef
  set h : Ω → ℝ := fun x => max (-(f x)) 0 with hhdef
  have hgm : Measurable g := hf.max measurable_const
  have hhm : Measurable h := hf.neg.max measurable_const
  have hgmem : MemLp g 2 pi := memLp_two_max_zero hf hmem
  have hhmem : MemLp h 2 pi := memLp_two_max_zero hf.neg hmem.neg
  have hgint := integrable_sq_sub_compProd hinv hgm hgmem
  have hhint := integrable_sq_sub_compProd hinv hhm hhmem
  have hfint := integrable_sq_sub_compProd hinv hf hmem
  have hmeas : Measurable fun p : Ω × Ω => ENNReal.ofReal ((g p.1 - g p.2) ^ 2) :=
    (((hgm.comp measurable_fst).sub (hgm.comp measurable_snd)).pow_const 2).ennreal_ofReal
  -- the `ℝ≥0∞` inequality
  have hkey : ∫⁻ p, ENNReal.ofReal ((g p.1 - g p.2) ^ 2) ∂(pi ⊗ₘ P)
      + ∫⁻ p, ENNReal.ofReal ((h p.1 - h p.2) ^ 2) ∂(pi ⊗ₘ P)
      ≤ ∫⁻ p, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) ∂(pi ⊗ₘ P) := by
    rw [← lintegral_add_left hmeas]
    refine lintegral_mono fun p => ?_
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (sq_posPart_sub_add_sq_negPart_sub_le (f p.1) (f p.2))
  rw [← ofReal_two_mul_dirichletFormReal P pi hgint,
    ← ofReal_two_mul_dirichletFormReal P pi hhint,
    ← ofReal_two_mul_dirichletFormReal P pi hfint,
    ← ENNReal.ofReal_add (by linarith [dirichletFormReal_nonneg P pi g])
      (by linarith [dirichletFormReal_nonneg P pi h]),
    ENNReal.ofReal_le_ofReal_iff (by linarith [dirichletFormReal_nonneg P pi f])] at hkey
  linarith

/-- **The `L²` isoperimetric inequality, in `ℝ`.**  For a reversible chain with finite
conductance and a measurable `g ≥ 0` in `L²(pi)` supported on a set of measure at most
`1/2`,

`Φ² ∫ g² dpi ≤ 2 E(g, g)`.

This is `sq_conductance_mul_lintegral_sq_le_lintegral_sub_sq` transported through the `L²`
bridge `ofReal_two_mul_dirichletFormReal`; the integrability side condition is discharged by
`integrable_sq_sub_compProd`, so no new hypothesis appears.

`Φ ≠ ⊤` is needed only to read `Φ` as a real number: `Φ = ⊤` happens exactly when no
measurable set has measure in `(0, 1/2]` (`conductance_eq_top_of_isEmpty`), and then
`Φ.toReal = 0` and the statement is trivially true anyway. -/
theorem sq_conductance_mul_integral_sq_le_two_mul_dirichletFormReal {P : Kernel Ω Ω}
    [IsMarkovKernel P] {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {g : Ω → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hmem : MemLp g 2 pi)
    (hsupp : pi {x | 0 < g x} ≤ 1 / 2) (hfin : conductance P pi ≠ ⊤) :
    (conductance P pi).toReal ^ 2 * ∫ x, g x ^ 2 ∂pi ≤ 2 * dirichletFormReal P pi g := by
  have hkey := sq_conductance_mul_lintegral_sq_le_lintegral_sub_sq hrev hg hg0 hsupp
    (lintegral_sq_ne_top_of_memLp hmem)
  rw [← ofReal_two_mul_dirichletFormReal P pi
      (integrable_sq_sub_compProd hrev.invariant hg hmem),
    ← ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _),
    show conductance P pi ^ 2
        = ENNReal.ofReal ((conductance P pi).toReal ^ 2) by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin],
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by linarith [dirichletFormReal_nonneg P pi g])] at hkey
  exact hkey

/-! ### The median shift, and the Rayleigh quotient of a measurable `f` -/

/-- `(a⁺)² + (a⁻)² = a²`.  Pure arithmetic; it is what turns `∫ (f − m)²` into
`∫ (f−m)⁺ ² + ∫ (f−m)⁻ ²`. -/
theorem sq_max_zero_add_sq_max_neg_zero (a : ℝ) : max a 0 ^ 2 + max (-a) 0 ^ 2 = a ^ 2 := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -a ≤ 0)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -a)]; ring

/-- **Cheeger's hard direction at a single measurable `f`**:

`Φ²/2 ≤ E(f,f) / Var(f)`.

Shift `f` by a median `m` (`exists_median`) and split into `g = (f−m)⁺` and `h = (f−m)⁻`.
Both are nonnegative, in `L²`, and supported on sets of measure at most `1/2`, so the `L²`
isoperimetric inequality applies to each; the variance is at most `∫ g² + ∫ h²`
(`varianceReal_le_integral_sub_sq` and `sq_max_zero_add_sq_max_neg_zero`), and the energies
add up to at most `E(f,f)` (`dirichletFormReal_posPart_add_negPart_le`, using that the
Dirichlet form ignores the shift).

`Measurable f` — rather than just `AEStronglyMeasurable` — is needed for `exists_median`;
`sq_conductance_div_two_le_rayleighQuotient` removes it by passing to a measurable
representative. -/
theorem sq_conductance_div_two_le_rayleighQuotient_of_measurable {P : Kernel Ω Ω}
    [IsMarkovKernel P] {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hfin : conductance P pi ≠ ⊤) {f : Ω → ℝ} (hf : Measurable f) (hmem : MemLp f 2 pi)
    (hv : varianceReal pi f ≠ 0) :
    (conductance P pi).toReal ^ 2 / 2 ≤ rayleighQuotient P pi f := by
  obtain ⟨m, hm1, hm2⟩ := exists_median (pi := pi) hf
  set u : Ω → ℝ := fun x => f x - m with hudef
  have hum : Measurable u := hf.sub measurable_const
  have humem : MemLp u 2 pi := hmem.sub (memLp_const m)
  set g : Ω → ℝ := fun x => max (u x) 0 with hgdef
  set h : Ω → ℝ := fun x => max (-(u x)) 0 with hhdef
  have hgm : Measurable g := hum.max measurable_const
  have hhm : Measurable h := hum.neg.max measurable_const
  have hgmem : MemLp g 2 pi := memLp_two_max_zero hum humem
  have hhmem : MemLp h 2 pi := memLp_two_max_zero hum.neg humem.neg
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_max_right _ _
  have hh0 : ∀ x, 0 ≤ h x := fun x => le_max_right _ _
  -- the two supports are the two median half-lines
  have hgsupp : pi {x : Ω | 0 < g x} ≤ 1 / 2 := by
    have hset : {x : Ω | 0 < g x} = {x : Ω | m < f x} := by
      ext x; simp [hgdef, hudef]
    rw [hset]; exact hm1
  have hhsupp : pi {x : Ω | 0 < h x} ≤ 1 / 2 := by
    have hset : {x : Ω | 0 < h x} = {x : Ω | f x < m} := by
      ext x; simp [hhdef, hudef]
    rw [hset]; exact hm2
  -- the variance is dominated by the two `L²` masses
  have hvar : varianceReal pi f ≤ (∫ x, g x ^ 2 ∂pi) + ∫ x, h x ^ 2 ∂pi := by
    have h1 := varianceReal_le_integral_sub_sq (pi := pi) hf.aestronglyMeasurable m
    have h2 : ∫ x, (f x - m) ^ 2 ∂pi = (∫ x, g x ^ 2 ∂pi) + ∫ x, h x ^ 2 ∂pi := by
      rw [← integral_add hgmem.integrable_sq hhmem.integrable_sq]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
        (sq_max_zero_add_sq_max_neg_zero (u x)).symm)
    linarith
  -- the energies of the two halves add up to at most the energy of `f`
  have hue : dirichletFormReal P pi u = dirichletFormReal P pi f := by
    simpa [hudef, sub_eq_add_neg] using dirichletFormReal_add_const P pi f (-m)
  have henergy : dirichletFormReal P pi g + dirichletFormReal P pi h
      ≤ dirichletFormReal P pi f :=
    hue ▸ dirichletFormReal_posPart_add_negPart_le hrev.invariant hum humem
  -- the `L²` isoperimetric inequality on each half
  have hgineq := sq_conductance_mul_integral_sq_le_two_mul_dirichletFormReal hrev hgm hg0
    hgmem hgsupp hfin
  have hhineq := sq_conductance_mul_integral_sq_le_two_mul_dirichletFormReal hrev hhm hh0
    hhmem hhsupp hfin
  have hvpos : 0 < varianceReal pi f := (varianceReal_nonneg pi f).lt_of_ne (Ne.symm hv)
  rw [rayleighQuotient, div_le_div_iff₀ (by norm_num) hvpos]
  nlinarith [mul_le_mul_of_nonneg_left hvar (sq_nonneg (conductance P pi).toReal)]

/-! ### From a measurable `f` to an arbitrary `f ∈ L²(pi)`

`AdmissibleL2` asks only for `MemLp f 2 pi`, so its members need not be measurable — but
`exists_median` does need measurability.  The gap is closed by passing to the measurable
representative `hmem.aestronglyMeasurable.mk f`, which is legitimate because
`dirichletFormReal` is a.e.-congruent *when `pi` is invariant*: a `pi`-null set is `P x`-null
for `pi`-a.e. `x`, so an a.e. modification of `f` does not change the inner integrals either.
Without invariance this would be false. -/

/-- **A `pi`-null set is `P x`-null for `pi`-almost every `x`**, when `pi` is invariant.
Hence an a.e. identity under `pi` upgrades to an a.e. identity under `P x` for a.e. `x`. -/
theorem ae_ae_eq_of_invariant {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {f f' : Ω → ℝ}
    (hff : f =ᵐ[pi] f') : ∀ᵐ x ∂pi, f =ᵐ[P x] f' := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hff)
  have hbind : ∫⁻ x, P x N ∂pi = 0 := by
    rw [← Measure.bind_apply hNm (Kernel.measurable P).aemeasurable, hinv.def, hN0]
  have := (lintegral_eq_zero_iff (Kernel.measurable_coe P hNm)).1 hbind
  filter_upwards [this] with x hx
  exact measure_mono_null hsub hx

/-- **The real Dirichlet form only depends on the `pi`-a.e. class of `f`**, for an invariant
`pi`.  This is what lets the hard direction be proved for a measurable representative and
transported back to an arbitrary member of `AdmissibleL2`. -/
theorem dirichletFormReal_congr_ae {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {f f' : Ω → ℝ}
    (hff : f =ᵐ[pi] f') : dirichletFormReal P pi f = dirichletFormReal P pi f' := by
  rw [dirichletFormReal, dirichletFormReal]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hff, ae_ae_eq_of_invariant hinv hff] with x hx hax
  refine integral_congr_ae ?_
  filter_upwards [hax] with y hy
  rw [hx, hy]

/-- The Rayleigh quotient only depends on the `pi`-a.e. class of `f`. -/
theorem rayleighQuotient_congr_ae {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hinv : Kernel.Invariant P pi) {f f' : Ω → ℝ}
    (hff : f =ᵐ[pi] f') : rayleighQuotient P pi f = rayleighQuotient P pi f' := by
  rw [rayleighQuotient, rayleighQuotient, dirichletFormReal_congr_ae hinv hff, varianceReal,
    varianceReal, ProbabilityTheory.variance_congr hff]

/-- **Cheeger's hard direction at a single `f ∈ L²(pi)`**, with no measurability hypothesis:

`Φ²/2 ≤ E(f,f) / Var(f)`.

`sq_conductance_div_two_le_rayleighQuotient_of_measurable` with the measurability removed by
`rayleighQuotient_congr_ae`. -/
theorem sq_conductance_div_two_le_rayleighQuotient {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hfin : conductance P pi ≠ ⊤) {f : Ω → ℝ} (hmem : MemLp f 2 pi)
    (hv : varianceReal pi f ≠ 0) :
    (conductance P pi).toReal ^ 2 / 2 ≤ rayleighQuotient P pi f := by
  have hff : f =ᵐ[pi] hmem.aestronglyMeasurable.mk f := hmem.aestronglyMeasurable.ae_eq_mk
  have hf'm : Measurable (hmem.aestronglyMeasurable.mk f) :=
    hmem.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hf'mem : MemLp (hmem.aestronglyMeasurable.mk f) 2 pi := hmem.ae_eq hff
  have hv' : varianceReal pi (hmem.aestronglyMeasurable.mk f) ≠ 0 := by
    rwa [varianceReal, ← ProbabilityTheory.variance_congr hff]
  rw [rayleighQuotient_congr_ae hrev.invariant hff]
  exact sq_conductance_div_two_le_rayleighQuotient_of_measurable hrev hfin hf'm hf'mem hv'

/-! ## The hard direction of Cheeger -/

/-- **The hard direction of Cheeger's inequality**:

`Φ²/2 ≤ spectralGap P pi`

for a reversible Markov chain on a probability space, provided some `f ∈ L²(pi)` has nonzero
variance (`hne`), i.e. the infimum defining `spectralGap` is over a non-empty family.

That hypothesis cannot be dropped and is not a disguised assumption of the conclusion: over
`ℝ`, `sInf ∅ = 0`, so on a space where every `L²` function is a.e. constant `spectralGap`
is the junk value `0` while `Φ` need not be — see the module docstring's design note.  The
non-vacuity witness `exists_spectralGap_pos` exhibits a chain where `hne` holds.

No hypothesis here mentions the spectral gap, the conductance, or an isoperimetric constant:
the ingredients are the co-area formula, the `L¹` isoperimetric inequality, a median, and
Cauchy–Schwarz, each proved above.

Together with `ofReal_spectralGap_le_two_mul_conductance` this is the two-sided Cheeger
inequality `Φ²/2 ≤ gap ≤ 2 Φ`. -/
theorem sq_conductance_div_two_le_spectralGap {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hne : (rayleighSet P pi).Nonempty) :
    (conductance P pi).toReal ^ 2 / 2 ≤ spectralGap P pi := by
  rcases eq_or_ne (conductance P pi) ⊤ with hc | hc
  · simpa [hc] using spectralGap_nonneg P pi
  exact le_spectralGap P pi hne fun f hf hv =>
    sq_conductance_div_two_le_rayleighQuotient hrev hc hf hv

/-- **Cheeger's inequality, both directions.**  `Φ²/2 ≤ gap ≤ 2 Φ`. -/
theorem cheeger {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω} [IsProbabilityMeasure pi]
    (hrev : IsReversible P pi) (hne : (rayleighSet P pi).Nonempty) :
    (conductance P pi).toReal ^ 2 / 2 ≤ spectralGap P pi ∧
      ENNReal.ofReal (spectralGap P pi) ≤ 2 * conductance P pi :=
  ⟨sq_conductance_div_two_le_spectralGap hrev hne,
    ofReal_spectralGap_le_two_mul_conductance hrev⟩

/-! ### A non-vacuity witness for the hard direction (`CLAUDE.md` §11)

The hard direction is quantified over chains satisfying `hne`; the two-point chain shows the
hypothesis is satisfiable with both sides finite and nonzero, so the statement is not
vacuous. -/

/-- The admissible family of the instantly mixing chain on `Bool` is non-empty. -/
theorem rayleighSet_const_piHalf_nonempty :
    (rayleighSet (Kernel.const Bool piHalf) piHalf).Nonempty := by
  refine ⟨rayleighQuotient (Kernel.const Bool piHalf) piHalf
    (Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ))),
    Set.indicator ({true} : Set Bool) (fun _ => (1 : ℝ)),
    ⟨memLp_two_indicator (measurableSet_singleton true), ?_⟩, rfl⟩
  rw [varianceReal_indicator_piHalf]
  norm_num

/-- **The hard direction is non-vacuous.**  On `Kernel.const Bool piHalf` the conductance is
`1/2` and the spectral gap is `1`, so `Φ²/2 ≤ gap` reads `1/8 ≤ 1`: both sides are finite,
the left one is nonzero, and the hypotheses are all satisfied. -/
theorem sq_conductance_div_two_le_spectralGap_const_piHalf :
    ((conductance (Kernel.const Bool piHalf) piHalf).toReal) ^ 2 / 2 = 1 / 8 ∧
      spectralGap (Kernel.const Bool piHalf) piHalf = 1 ∧
      ((conductance (Kernel.const Bool piHalf) piHalf).toReal) ^ 2 / 2
        ≤ spectralGap (Kernel.const Bool piHalf) piHalf := by
  refine ⟨?_, spectralGap_const_piHalf, sq_conductance_div_two_le_spectralGap
    (isReversible_const piHalf) rayleighSet_const_piHalf_nonempty⟩
  rw [conductance_const_piHalf]
  norm_num

end Arlib.MarkovChains
