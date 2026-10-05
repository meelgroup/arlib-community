/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyWalk
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.SharpIsoperimetry
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Cousins–Vempala's `thm:speedyconductance`, conditional on the sharp isoperimetric inequality

Cousins–Vempala, *Gaussian Cooling and `O*(n³)` Algorithms for Volume and Gaussian Volume*,
Theorem `thm:speedyconductance` (`1409.6011/vol3_journal.tex:624`, proof at `:628`):

> Let `K` be a convex body with `Bₙ ⊆ K ⊆ 4σ√n Bₙ`.  The conductance of the speedy walk
> applied to `K` with Gaussian density `N(0,σ²I)` and `δ ≤ σ/(8√n)` steps is `Ω(δ/(σ√n))`.

This file carries out that proof.  The result it lands,
`Arlib.MarkovChains.conductance_speedyGaussian_ge`, is **conditional**: its two inputs with
content — the one-step overlap estimate `cor:overlap` (`vol3_journal.tex:612`) and the sharp
isoperimetric inequality `thm:iso` (`:467`) — are both hypotheses, written out inline.  What
is *proved* here is everything between them and the conductance: the three-way partition, the
flow accounting, the degenerate branch, and the arithmetic of the step `d`.

## This is not a polynomial-time result, and nothing here may be quoted as one

`thm:iso` is **not proved in this repository.**  `Arlib.gaussianRestricted_isoperimetry`
(`Arlib/Convexity/SharpIsoperimetry.lean`) assembles it, but carries four undischarged
hypotheses (`hloc`, `hcombinatorial`, `h1d1`, `h1d2`); today none of the four is closed.  The
hypothesis `hiso` below is *exactly* that theorem's conclusion at `d = δ·ln 2/√n`, so it
composes with `Arlib.gaussianRestricted_isoperimetry` by `exact` the moment those four land —
and not before.

Every conductance constant that is actually *proved* in this repository is exponentially small
in `n` (`Arlib/MarkovChains/Continuous/MetropolisConductance.lean`;
`Arlib/Convexity/GaussianCooling/Unblock.lean:591–596`, "this is not a polynomial-time
result").  The theorem below would change that picture, but only once `hiso` — and `hoverlap`
— are discharged.  Until then it is a conditional reduction, not a rate improvement.  **No
statement in this file asserts, or may be quoted as asserting, a polynomial mixing time.**

## What is assumed, and what is proved

`conductance_speedyGaussian_ge` has exactly two hypotheses that are not bookkeeping.

* **`hoverlap` — `cor:overlap`** (`vol3_journal.tex:612`).  For `u ∈ S ∩ K` and `v ∈ K \ S`
  with `‖u − v‖ < δ/√n` and `d_h(u,v) < 1/4`, one step satisfies
  `P_u(Sᶜ) + P_v(S) ≥ 1/20`.  The paper derives it from `lem:overlap` (`:581`, itself KLS95
  Lemma 3.5) and `lem:filter`.  **This repository has no analogue.**
  `Arlib.MarkovChains.one_le_speedyWalk_add_speedyWalk_compl` (`SpeedyWalk.lean`) is the
  uniform, convexity-based substitute and reaches only separation `δ/n`, a factor `√n` short
  — the caveat already recorded in `BallWalkConductance.lean`'s docstring;
  `Arlib.MarkovChains.mul_ell_le_metropolisGaussian_add_metropolisGaussian_compl`
  (`MetropolisConductance.lean`) is the same estimate for the *Metropolis* walk and likewise
  loses `√n`.  Neither delivers `cor:overlap`, so it is assumed.
* **`hiso` — `thm:iso`** at `d = δ·ln 2/√n`, in exactly the shape
  `Arlib.gaussianRestricted_isoperimetry` concludes.

Everything else — reversibility, the density formula for `π`, measurability — is bookkeeping,
and the conductance assembly itself is proved.

## Main results

* `Arlib.MarkovChains.two_mul_log_two_le_sqrt_natCast`,
  `Arlib.MarkovChains.four_mul_isoStep_div_sigma_le_quarter`,
  `Arlib.MarkovChains.isoStep_conductance_le_inv_160` — the arithmetic of the step
  `d = δ·ln 2/√n`: its density branch is capped below `1/4`, and the resulting conductance
  never exceeds the degenerate branch's `1/160`.
* `Arlib.MarkovChains.ofReal_div_mul_div_le` — the `ℝ≥0∞` bridge from `thm:iso`'s real-integral
  conclusion to the normalised measure `π`.
* `Arlib.MarkovChains.measure_sdiff_add_measure_sdiff_le_flow` — the flow accounting for the
  three-way partition, from `mul_measure_add_measure_le_mul_flow`.
* `Arlib.MarkovChains.measure_le_flow_of_le_two_mul` — **the degenerate branch**,
  `φ(S) ≥ 1/160`, independent of `hiso`.
* `Arlib.MarkovChains.conductance_speedyGaussian_ge` — **the theorem**:
  `Φ ≥ δ·ln 2/(640·σ·√n)`.
* `Arlib.MarkovChains.speedyGaussian_params_satisfiable`,
  `Arlib.MarkovChains.exists_conductance_speedyGaussian_pos` — the non-vacuity witnesses.

## Three discrepancies with the printed proof

**(i) The partition thresholds must be `1/40`, not `1/20`.**  The paper sets
`S₁ = {x ∈ S : P_x(S̄) < 1/20}` and `S₂ = {x ∈ S̄ : P_x(S) < 1/20}`, and then asserts that
`cor:overlap` — which gives `P_u(S̄) + P_v(S) > 1/20` — forces `u ∈ S₁, v ∈ S₂` to be
separated.  It does not: two quantities each below `1/20` sum to less than `1/10`, which is
consistent with a sum exceeding `1/20`.  With the thresholds halved to `1/40` the sum is below
`1/20` and the contradiction is real.  That is what is done here; it costs a factor `2` in
both branches.

**(ii) `φ(S) ≥ (1/40)·π(S₃)/π(S₁)` is `π(S₁)` where it should be `π(S)`.**  The paper's final
chain (`vol3_journal.tex:660`) divides the flow by `π(S₁)`, but `φ(S) = Φ(S)/π(S)` and
`π(S₁) ≤ π(S)`, so the step increases the quantity being bounded below.  Restoring `π(S)`
costs the factor `π(S)/π(S₁) ≤ 2`.

Together (i) and (ii) turn the paper's `d/(160σ)` into `d/(640σ)` and its
`φ ≥ δ/(250σ√n)` into `φ ≥ δ·ln 2/(640σ√n) ≥ δ/(924σ√n)`.  The conclusion `Ω(δ/(σ√n))` is
unaffected; only the constant moves.

**(iii) The `σ` in `thm:iso`'s density branch.**  Already recorded in
`Arlib/Convexity/SharpIsoperimetry.lean`'s docstring: the printed disjunct `d_h ≥ 4d√n` is
correct only at `σ = 1`, and the corrected form is `d_h ≥ 4(d/σ)√n`, with the paper's
`d = min{δ ln 2/√n, 1/(16√n)}` becoming `min{δ ln 2/√n, σ/(16√n)}`.  Under `δ ≤ σ/(8√n)` the
first term binds for every `n ≥ 2` (`16δ ln 2 ≤ 2σ ln 2/√n ≤ σ`; checked at a concrete
instance by `speedyGaussian_params_satisfiable`), so `d = δ·ln 2/√n` exactly as printed and
the conductance is unchanged — which is why only the `d` chosen here is ever needed.

## Non-vacuity, and the `densDist_le_one` cap

`Arlib.densDist_le_one` makes `thm:iso`'s density branch **unsatisfiable** once
`4(d/σ)√n > 1`.  At `d = δ·ln 2/√n` with `δ ≤ σ/(8√n)` one has
`4(d/σ)√n = 4δ·ln 2/σ ≤ ln 2/(2√n) ≤ 1/4 < 1` for `n ≥ 2`
(`four_mul_isoStep_div_sigma_le_quarter`), so the branch is *inside* the cap and carries
content — this is exactly why the paper caps `d`.  The `1/4` is moreover the threshold
`cor:overlap` supplies, and the two match only because `n ≥ 2`: at `n = 1` one has
`ln 2/2 = 0.347 > 1/4` and the argument fails, which is why `hn : 2 ≤ n` is stated.

`speedyGaussian_params_satisfiable` checks that `Bₙ ⊆ K ⊆ 4σ√n Bₙ` (i.e. `1 ≤ 4σ√n`),
`δ ≤ σ/(8√n)`, `d = min{δ ln 2/√n, σ/(16√n)} = δ ln 2/√n`, `4(d/σ)√n ≤ 1/4 ≤ 1` and a
strictly positive conductance bound hold **simultaneously** at `n = 4`, `σ = 1`, `δ = 1/16`.
`exists_conductance_speedyGaussian_pos` goes further and *applies* the theorem to a concrete
kernel and measure, discharging **every** hypothesis including `hoverlap` and `hiso`, and
obtains a strictly positive lower bound on a genuine conductance.  So the theorem is not
vacuous.

## References

Cousins and Vempala, *Gaussian Cooling and `O*(n³)` Algorithms for Volume and Gaussian
Volume*, §4.1 (`1409.6011/vol3_journal.tex:509–700`).
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## 1. The arithmetic of the step `d = δ·ln 2/√n` -/

/-- `2 ln 2 ≤ √n` for `n ≥ 2`.  Numerically `1.3863 ≤ 1.4142`; this is the inequality that
makes `thm:iso`'s density branch fit under `cor:overlap`'s `1/4` threshold, and it is the
reason `n ≥ 2` is assumed throughout (at `n = 1` it is false). -/
theorem two_mul_log_two_le_sqrt_natCast {n : ℕ} (hn : 2 ≤ n) :
    2 * Real.log 2 ≤ Real.sqrt n := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : Real.sqrt 2 ≤ Real.sqrt n := Real.sqrt_le_sqrt h2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h14 : (1.4 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hlog := Real.log_two_lt_d9
  linarith

/-- **`thm:iso`'s density branch sits under `cor:overlap`'s threshold.**  At
`d = δ·ln 2/√n` and `δ ≤ σ/(8√n)`,

    4·(d/σ)·√n  =  4δ·ln 2/σ  ≤  ln 2/(2√n)  ≤  1/4    (n ≥ 2).

Both halves matter.  The upper bound `1/4` is what lets `cor:overlap`'s hypothesis
`d_h(u,v) < 1/4` be *implied* by the failure of the density branch; and since `1/4 < 1`, the
branch also stays inside the cap `Arlib.densDist_le_one` imposes, so it is not vacuous. -/
theorem four_mul_isoStep_div_sigma_le_quarter {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) :
    4 * ((δ * Real.log 2 / Real.sqrt n) / σ) * Real.sqrt n ≤ 1 / 4 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : 2 * Real.log 2 ≤ Real.sqrt n := two_mul_log_two_le_sqrt_natCast hn
  have hδ' : δ * (8 * Real.sqrt n) ≤ σ := by
    rw [le_div_iff₀ (by positivity)] at hδσ
    linarith
  have hrw : 4 * ((δ * Real.log 2 / Real.sqrt n) / σ) * Real.sqrt n
      = 4 * δ * Real.log 2 / σ := by
    field_simp
  rw [hrw, div_le_iff₀ hσ]
  -- `4 δ ln2 ≤ 2 δ √n ≤ σ/4`
  have h1 : 4 * δ * Real.log 2 ≤ 2 * δ * Real.sqrt n := by nlinarith
  nlinarith

/-- **The conductance the theorem certifies never exceeds the degenerate branch's `1/160`.**
Since `δ ≤ σ/(8√n)` and `√n ≥ 1`, `δ·ln 2/(640σ√n) ≤ 1/5120 ≤ 1/160`.  This is what lets the
two branches of the proof be combined into a *single* constant instead of a `min`. -/
theorem isoStep_conductance_le_inv_160 {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) :
    δ * Real.log 2 / (640 * σ * Real.sqrt n) ≤ 1 / 160 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at this
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ' : δ * (8 * Real.sqrt n) ≤ σ := by
    rw [le_div_iff₀ (by positivity)] at hδσ
    linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ## 2. The `ℝ≥0∞` bridge

`thm:iso` concludes about *real* integrals of the unnormalised density `h`; the conductance is
about the *probability measure* `π` with `π A = ∫_A h / ∫ h`.  The passage between the two is
purely arithmetic, and exact: both sides of `thm:iso` are homogeneous of degree two in `h`, so
dividing through by `(∫ h)²` loses nothing. -/

/-- **From `thm:iso`'s real form to the normalised measure.**  If
`c·(a₁·a₂) ≤ M·a₃` with `M > 0` and `a₁, a₂, c ≥ 0`, then in `ℝ≥0∞`

    c · (a₁/M) · (a₂/M)  ≤  a₃/M.

This is `thm:iso`'s conclusion divided by `M² = (∫ h)²`. -/
theorem ofReal_div_mul_div_le {M a₁ a₂ a₃ c : ℝ} (hM : 0 < M) (ha₁ : 0 ≤ a₁)
    (hc : 0 ≤ c) (hle : c * (a₁ * a₂) ≤ M * a₃) :
    ENNReal.ofReal c * (ENNReal.ofReal a₁ / ENNReal.ofReal M)
        * (ENNReal.ofReal a₂ / ENNReal.ofReal M)
      ≤ ENNReal.ofReal a₃ / ENNReal.ofReal M := by
  set M' : ℝ≥0∞ := ENNReal.ofReal M with hM'
  have hM'0 : M' ≠ 0 := by
    rw [hM']
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hM
  have hM'top : M' ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstep : ENNReal.ofReal c * ENNReal.ofReal a₁ * ENNReal.ofReal a₂
      ≤ M' * ENNReal.ofReal a₃ := by
    rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (mul_nonneg hc ha₁), hM',
      ← ENNReal.ofReal_mul hM.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc c * a₁ * a₂ = c * (a₁ * a₂) := by ring
      _ ≤ M * a₃ := hle
  calc ENNReal.ofReal c * (ENNReal.ofReal a₁ / M') * (ENNReal.ofReal a₂ / M')
      = (ENNReal.ofReal c * ENNReal.ofReal a₁ * ENNReal.ofReal a₂) * (M'⁻¹ * M'⁻¹) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
    _ ≤ (M' * ENNReal.ofReal a₃) * (M'⁻¹ * M'⁻¹) := by gcongr
    _ = ENNReal.ofReal a₃ * (M' * M'⁻¹) * M'⁻¹ := by ring
    _ = ENNReal.ofReal a₃ * M'⁻¹ := by
        rw [ENNReal.mul_inv_cancel hM'0 hM'top, mul_one]
    _ = ENNReal.ofReal a₃ / M' := by rw [ENNReal.div_eq_inv_mul]; ring

/-! ## 3. The flow accounting and the degenerate branch

Both are `hiso`-free.  The first is `mul_measure_add_measure_le_mul_flow`
(`BallWalkConductance.lean`, stated for an arbitrary reversible Markov kernel on an arbitrary
measurable space) specialised to the escape threshold `1/40`; the second is the paper's
`φ(S) ≥ 1/80` branch (`vol3_journal.tex:650`), at the corrected threshold, hence `1/160`. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The flow accounting of the three-way partition.**  If every point of `S \ A` escapes `S`
with probability at least `1/40`, and every point of `Sᶜ \ B` enters `S` with probability at
least `1/40`, then

    π(S \ A) + π(Sᶜ \ B)  ≤  80 · Φ(S, Sᶜ).

Division-free: the thresholds are written `1 ≤ 40·P_x(·)`.  This is
`vol3_journal.tex:652–655`, where `A = S₁ ∪ Kᶜ` and `B = S₂ ∪ Kᶜ`. -/
theorem measure_sdiff_add_measure_sdiff_le_flow (P : Kernel Ω Ω) [IsMarkovKernel P]
    (pi : Measure Ω) (hrev : IsReversible P pi) {S A B : Set Ω} (hS : MeasurableSet S)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA' : ∀ x ∈ S \ A, 1 ≤ 40 * P x Sᶜ) (hB' : ∀ x ∈ Sᶜ \ B, 1 ≤ 40 * P x S) :
    pi (S \ A) + pi (Sᶜ \ B) ≤ 80 * flow P pi S Sᶜ := by
  have h := mul_measure_add_measure_le_mul_flow P pi hrev hS hA hB hA' hB'
  rw [one_mul] at h
  calc pi (S \ A) + pi (Sᶜ \ B) ≤ 2 * (40 * flow P pi S Sᶜ) := h
    _ = 80 * flow P pi S Sᶜ := by ring

/-- **The degenerate branch of `thm:speedyconductance`** (`vol3_journal.tex:650`): if `S` is
not mostly covered by `S₁` — precisely, if `π(S) ≤ 2·(π(S \ A) + π(Sᶜ \ B))` — then the escape
flow alone already bounds the conductance from below, with **no isoperimetric input**:

    π(S)  ≤  160 · Φ(S, Sᶜ),    i.e.  φ(S) ≥ 1/160.

The paper's constant is `1/80`, from thresholds `1/20`; at the corrected thresholds `1/40`
(module docstring, discrepancy (i)) it is `1/160`. -/
theorem measure_le_flow_of_le_two_mul (P : Kernel Ω Ω) [IsMarkovKernel P] (pi : Measure Ω)
    (hrev : IsReversible P pi) {S A B : Set Ω} (hS : MeasurableSet S) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hA' : ∀ x ∈ S \ A, 1 ≤ 40 * P x Sᶜ)
    (hB' : ∀ x ∈ Sᶜ \ B, 1 ≤ 40 * P x S)
    (hsmall : pi S ≤ 2 * (pi (S \ A) + pi (Sᶜ \ B))) :
    pi S ≤ 160 * flow P pi S Sᶜ := by
  have h := measure_sdiff_add_measure_sdiff_le_flow P pi hrev hS hA hB hA' hB'
  calc pi S ≤ 2 * (pi (S \ A) + pi (Sᶜ \ B)) := hsmall
    _ ≤ 2 * (80 * flow P pi S Sᶜ) := by gcongr
    _ = 160 * flow P pi S Sᶜ := by ring

/-! ## 4. The theorem -/

/-- **Cousins–Vempala's `thm:speedyconductance`** (`vol3_journal.tex:624`), assembled.

Let `π` be the probability measure with density proportional to `h = ℓ·f` on `ℝⁿ`, let `P` be
a Markov kernel reversible for `π` and supported on a measurable `K` (in the sense
`π(Kᶜ) = 0`), and let `δ ≤ σ/(8√n)` with `n ≥ 2`.  Then

    Φ(P, π)  ≥  δ·ln 2 / (640·σ·√n).

Two hypotheses carry content, both written out inline; neither is a `def` or a named `Prop`.

* `hoverlap` — **`cor:overlap`** (`vol3_journal.tex:612`): a pair `u ∈ S ∩ K`, `v ∈ K \ S`
  with `‖u − v‖ < δ/√n` and `d_h(u,v) < 1/4` has `P_u(Sᶜ) + P_v(S) ≥ 1/20`, here written
  division-free as `1 ≤ 20·(P_u(Sᶜ) + P_v(S))`.  **Not proved in this repository**; see the
  module docstring.
* `hiso` — **`thm:iso`** (`vol3_journal.tex:467`) at `d = δ·ln 2/√n`, in exactly the shape
  `Arlib.gaussianRestricted_isoperimetry` concludes, so that it composes with that theorem by
  `exact` once its four external inputs are discharged.  **Not proved in this repository.**

The remaining hypotheses are bookkeeping: `hh0` (the density is nonnegative), `hmass` (it has
positive total mass), `hpi` (`π` really is the normalised `h`-measure — this is what makes
`π` a probability measure, so no `IsProbabilityMeasure` instance is assumed), `hrev`
(detailed balance) and measurability.

**The constant.**  `δ·ln 2/(640·σ·√n) ≥ δ/(924·σ·√n)`.  The paper prints `δ/(250σ√n)`; the
factor-`4` difference is two separate slips in its proof, both corrected here and both
recorded in the module docstring.  This is a bound of the shape `Ω(δ/(σ√n))` **conditional on
`hoverlap` and `hiso`**; it is not, and may not be quoted as, a polynomial-time statement. -/
theorem conductance_speedyGaussian_ge {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hmass : 0 < ∫ x, h x)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) [IsMarkovKernel P]
    (pi : Measure (EuclideanSpace ℝ (Fin n)))
    (hpi : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      pi A = ENNReal.ofReal (∫ x in A, h x) / ENNReal.ofReal (∫ x, h x))
    (hrev : IsReversible P pi) (hpiK : pi Kᶜ = 0)
    (hoverlap : ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n → densDist h u v < 1 / 4 →
      1 ≤ 20 * (P u Tᶜ + P v T))
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n ≤ densDist h u v) →
      δ * Real.log 2 / Real.sqrt n / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x)
        ≤ (∫ x, h x) * ∫ x in S₃, h x) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ≤ conductance P pi := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMne : ENNReal.ofReal (∫ x, h x) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hmass
  have hMtop : ENNReal.ofReal (∫ x, h x) ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI : IsProbabilityMeasure pi :=
    ⟨by rw [hpi _ MeasurableSet.univ, setIntegral_univ, ENNReal.div_self hMne hMtop]⟩
  -- the certified constant, written as `c/640`
  set c : ℝ≥0∞ := ENNReal.ofReal (δ * Real.log 2 / Real.sqrt n / σ) with hcdef
  have hcnn : 0 ≤ δ * Real.log 2 / Real.sqrt n / σ :=
    div_nonneg (div_nonneg (mul_nonneg hδ.le hlogpos.le) (Real.sqrt_nonneg _)) hσ.le
  have hconst : ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) = c / 640 := by
    rw [hcdef, show (640 : ℝ≥0∞) = ENNReal.ofReal (640 : ℝ) by simp,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 640)]
    congr 1
    field_simp
  have h160 : ENNReal.ofReal ((1 : ℝ) / 160) = (1 : ℝ≥0∞) / 160 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 160), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat]
  have hcle : c / 640 ≤ (1 : ℝ≥0∞) / 160 := by
    rw [← hconst, ← h160]
    exact ENNReal.ofReal_le_ofReal (isoStep_conductance_le_inv_160 hn hσ hδ hδσ)
  have hswap : ∀ a b e : ℝ≥0∞, a / e * b = a * b / e := by
    intro a b e
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  refine le_conductance P pi fun S hSm hSpos hShalf => ?_
  have hpitop : pi S ≠ ⊤ := measure_ne_top _ _
  have hSc : (1 : ℝ≥0∞) / 2 ≤ pi Sᶜ := by
    have hcompl : pi S + pi Sᶜ = 1 := by rw [measure_add_measure_compl hSm, measure_univ]
    have h1 : (1 : ℝ≥0∞) / 2 + 1 / 2 ≤ 1 / 2 + pi Sᶜ := by
      calc (1 : ℝ≥0∞) / 2 + 1 / 2 = 1 := ENNReal.add_halves 1
        _ = pi S + pi Sᶜ := hcompl.symm
        _ ≤ 1 / 2 + pi Sᶜ := by gcongr
    exact (ENNReal.add_le_add_iff_left (by simp)).1 h1
  -- the paper's three-way partition, at the corrected threshold `1/40`
  set S1 : Set (EuclideanSpace ℝ (Fin n)) := (S ∩ K) ∩ {x | 40 * P x Sᶜ < 1} with hS1def
  set S2 : Set (EuclideanSpace ℝ (Fin n)) := (K \ S) ∩ {x | 40 * P x S < 1} with hS2def
  have hS1m : MeasurableSet S1 :=
    (hSm.inter hK).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm.compl).const_mul 40) measurable_const)
  have hS2m : MeasurableSet S2 :=
    (hK.diff hSm).inter
      (measurableSet_lt ((Kernel.measurable_coe P hSm).const_mul 40) measurable_const)
  have hmem1 : ∀ x, x ∈ S1 ↔ ((x ∈ S ∧ x ∈ K) ∧ 40 * P x Sᶜ < 1) := by
    intro x
    rw [hS1def]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hmem2 : ∀ x, x ∈ S2 ↔ ((x ∈ K ∧ x ∉ S) ∧ 40 * P x S < 1) := by
    intro x
    rw [hS2def]
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
  set A : Set (EuclideanSpace ℝ (Fin n)) := S1 ∪ Kᶜ with hAdef
  set B : Set (EuclideanSpace ℝ (Fin n)) := S2 ∪ Kᶜ with hBdef
  have hAm : MeasurableSet A := hS1m.union hK.compl
  have hBm : MeasurableSet B := hS2m.union hK.compl
  have hA' : ∀ x ∈ S \ A, 1 ≤ 40 * P x Sᶜ := by
    rintro x ⟨hxS, hxA⟩
    have hxK : x ∈ K := by
      by_contra hc
      exact hxA (Or.inr hc)
    have hxS1 : x ∉ S1 := fun hc => hxA (Or.inl hc)
    by_contra hcon
    rw [not_le] at hcon
    exact hxS1 ((hmem1 x).2 ⟨⟨hxS, hxK⟩, hcon⟩)
  have hB' : ∀ x ∈ Sᶜ \ B, 1 ≤ 40 * P x S := by
    rintro x ⟨hxS, hxB⟩
    have hxK : x ∈ K := by
      by_contra hc
      exact hxB (Or.inr hc)
    have hxS2 : x ∉ S2 := fun hc => hxB (Or.inl hc)
    by_contra hcon
    rw [not_le] at hcon
    exact hxS2 ((hmem2 x).2 ⟨⟨hxK, hxS⟩, hcon⟩)
  have hflow := measure_sdiff_add_measure_sdiff_le_flow P pi hrev hSm hAm hBm hA' hB'
  -- coverings, using `π(Kᶜ) = 0`
  have hcov1 : pi S ≤ pi (S \ A) + pi S1 := by
    have hsub : S ⊆ ((S \ A) ∪ S1) ∪ Kᶜ := by
      intro x hx
      by_cases hxK : x ∈ K
      · by_cases hxS1 : x ∈ S1
        · exact Or.inl (Or.inr hxS1)
        · refine Or.inl (Or.inl ⟨hx, ?_⟩)
          rintro (hc | hc)
          · exact hxS1 hc
          · exact hc hxK
      · exact Or.inr hxK
    calc pi S ≤ pi (((S \ A) ∪ S1) ∪ Kᶜ) := measure_mono hsub
      _ ≤ pi ((S \ A) ∪ S1) + pi Kᶜ := measure_union_le _ _
      _ ≤ pi (S \ A) + pi S1 + pi Kᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi (S \ A) + pi S1 := by rw [hpiK, add_zero]
  have hcov2 : pi Sᶜ ≤ pi (Sᶜ \ B) + pi S2 := by
    have hsub : Sᶜ ⊆ ((Sᶜ \ B) ∪ S2) ∪ Kᶜ := by
      intro x hx
      by_cases hxK : x ∈ K
      · by_cases hxS2 : x ∈ S2
        · exact Or.inl (Or.inr hxS2)
        · refine Or.inl (Or.inl ⟨hx, ?_⟩)
          rintro (hc | hc)
          · exact hxS2 hc
          · exact hc hxK
      · exact Or.inr hxK
    calc pi Sᶜ ≤ pi (((Sᶜ \ B) ∪ S2) ∪ Kᶜ) := measure_mono hsub
      _ ≤ pi ((Sᶜ \ B) ∪ S2) + pi Kᶜ := measure_union_le _ _
      _ ≤ pi (Sᶜ \ B) + pi S2 + pi Kᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi (Sᶜ \ B) + pi S2 := by rw [hpiK, add_zero]
  have hcov3 : pi ((S1 ∪ S2)ᶜ) ≤ pi (S \ A) + pi (Sᶜ \ B) := by
    have hsub : (S1 ∪ S2)ᶜ ⊆ ((S \ A) ∪ (Sᶜ \ B)) ∪ Kᶜ := by
      intro x hx
      rw [Set.mem_compl_iff, Set.mem_union, not_or] at hx
      obtain ⟨hx1, hx2⟩ := hx
      by_cases hxK : x ∈ K
      · by_cases hxS : x ∈ S
        · refine Or.inl (Or.inl ⟨hxS, ?_⟩)
          rintro (hc | hc)
          · exact hx1 hc
          · exact hc hxK
        · refine Or.inl (Or.inr ⟨hxS, ?_⟩)
          rintro (hc | hc)
          · exact hx2 hc
          · exact hc hxK
      · exact Or.inr hxK
    calc pi ((S1 ∪ S2)ᶜ) ≤ pi (((S \ A) ∪ (Sᶜ \ B)) ∪ Kᶜ) := measure_mono hsub
      _ ≤ pi ((S \ A) ∪ (Sᶜ \ B)) + pi Kᶜ := measure_union_le _ _
      _ ≤ pi (S \ A) + pi (Sᶜ \ B) + pi Kᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi (S \ A) + pi (Sᶜ \ B) := by rw [hpiK, add_zero]
  -- the separation `cor:overlap` forces between `S₁` and `S₂`
  have hsep : ∀ u ∈ S1, ∀ v ∈ S2,
      δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
        4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n ≤ densDist h u v := by
    intro u hu v hv
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hdl : δ * Real.log 2 / Real.sqrt n / Real.log 2 = δ / Real.sqrt n := by
      field_simp
    rw [hdl] at hc1
    have hquarter : densDist h u v < 1 / 4 :=
      lt_of_lt_of_le hc2 (four_mul_isoStep_div_sigma_le_quarter hn hσ hδ hδσ)
    obtain ⟨⟨huS, huK⟩, hu40⟩ := (hmem1 u).1 hu
    obtain ⟨⟨hvK, hvS⟩, hv40⟩ := (hmem2 v).1 hv
    have hov := hoverlap S hSm u v huS huK hvK hvS hc1 hquarter
    have hge : (2 : ℝ≥0∞) ≤ 40 * P u Sᶜ + 40 * P v S := by
      calc (2 : ℝ≥0∞) = 2 * 1 := by norm_num
        _ ≤ 2 * (20 * (P u Sᶜ + P v S)) := by gcongr
        _ = 40 * P u Sᶜ + 40 * P v S := by ring
    have hlt : 40 * P u Sᶜ + 40 * P v S < 2 := by
      calc 40 * P u Sᶜ + 40 * P v S < 1 + 1 := ENNReal.add_lt_add hu40 hv40
        _ = 2 := by norm_num
    exact absurd hge (not_le.mpr hlt)
  -- `thm:iso`, transported to `π`
  have hpart : IsPartition3 Set.univ S1 S2 (S1 ∪ S2)ᶜ := by
    refine ⟨Set.union_compl_self _, ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x hx hx'
      exact ((hmem2 x).1 hx').1.2 ((hmem1 x).1 hx).1.1
    · rw [Set.disjoint_left]
      intro x hx hx'
      exact hx' (Or.inl hx)
    · rw [Set.disjoint_left]
      intro x hx hx'
      exact hx' (Or.inr hx)
  have hisoS := hiso S1 S2 (S1 ∪ S2)ᶜ hpart hS1m hS2m (hS1m.union hS2m).compl hsep
  have hmeas : c * pi S1 * pi S2 ≤ pi ((S1 ∪ S2)ᶜ) := by
    rw [hpi S1 hS1m, hpi S2 hS2m, hpi _ (hS1m.union hS2m).compl, hcdef]
    exact ofReal_div_mul_div_le hmass (integral_nonneg hh0) hcnn hisoS
  -- the two branches
  have hkey : pi S ≤ 160 * flow P pi S Sᶜ ∨ c * pi S ≤ 640 * flow P pi S Sᶜ := by
    by_cases hc1 : pi S ≤ 2 * pi (S \ A)
    · exact Or.inl (measure_le_flow_of_le_two_mul P pi hrev hSm hAm hBm hA' hB'
        (hc1.trans (by gcongr; exact le_self_add)))
    by_cases hc2 : pi Sᶜ ≤ 2 * pi (Sᶜ \ B)
    · refine Or.inl (measure_le_flow_of_le_two_mul P pi hrev hSm hAm hBm hA' hB' ?_)
      calc pi S ≤ pi Sᶜ := hShalf.trans hSc
        _ ≤ 2 * pi (Sᶜ \ B) := hc2
        _ ≤ 2 * (pi (S \ A) + pi (Sᶜ \ B)) := by gcongr; exact le_add_self
    right
    rw [not_le] at hc1 hc2
    have h1 : pi S < 2 * pi S1 := by
      have hstep : pi S + pi S < pi S + 2 * pi S1 := by
        calc pi S + pi S = 2 * pi S := (two_mul _).symm
          _ ≤ 2 * (pi (S \ A) + pi S1) := by gcongr
          _ = 2 * pi (S \ A) + 2 * pi S1 := by ring
          _ < pi S + 2 * pi S1 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc1
      exact (ENNReal.add_lt_add_iff_left hpitop).1 hstep
    have h2 : pi Sᶜ < 2 * pi S2 := by
      have hstep : pi Sᶜ + pi Sᶜ < pi Sᶜ + 2 * pi S2 := by
        calc pi Sᶜ + pi Sᶜ = 2 * pi Sᶜ := (two_mul _).symm
          _ ≤ 2 * (pi (Sᶜ \ B) + pi S2) := by gcongr
          _ = 2 * pi (Sᶜ \ B) + 2 * pi S2 := by ring
          _ < pi Sᶜ + 2 * pi S2 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc2
      exact (ENNReal.add_lt_add_iff_left (measure_ne_top _ _)).1 hstep
    have h3 : (1 : ℝ≥0∞) ≤ 4 * pi S2 := by
      have hhalf : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      calc (1 : ℝ≥0∞) = 2 * (1 / 2) := hhalf.symm
        _ ≤ 2 * pi Sᶜ := by gcongr
        _ ≤ 2 * (2 * pi S2) := by gcongr
        _ = 4 * pi S2 := by ring
    have hprod : pi S ≤ 8 * (pi S1 * pi S2) := by
      calc pi S = pi S * 1 := (mul_one _).symm
        _ ≤ 2 * pi S1 * (4 * pi S2) := mul_le_mul' h1.le h3
        _ = 8 * (pi S1 * pi S2) := by ring
    calc c * pi S ≤ c * (8 * (pi S1 * pi S2)) := by gcongr
      _ = 8 * (c * pi S1 * pi S2) := by ring
      _ ≤ 8 * pi ((S1 ∪ S2)ᶜ) := by gcongr
      _ ≤ 8 * (pi (S \ A) + pi (Sᶜ \ B)) := by gcongr
      _ ≤ 8 * (80 * flow P pi S Sᶜ) := by gcongr
      _ = 640 * flow P pi S Sᶜ := by ring
  rw [conductanceOn_apply, hconst,
    ENNReal.le_div_iff_mul_le (Or.inl hSpos.ne') (Or.inl hpitop)]
  rcases hkey with hcase | hcase
  · calc c / 640 * pi S ≤ (1 : ℝ≥0∞) / 160 * pi S := by gcongr
      _ = 1 * pi S / 160 := hswap _ _ _
      _ = pi S / 160 := by rw [one_mul]
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact hcase.trans_eq (mul_comm _ _)
  · calc c / 640 * pi S = c * pi S / 640 := hswap _ _ _
      _ ≤ flow P pi S Sᶜ := by
          rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          exact hcase.trans_eq (mul_comm _ _)

/-! ## 5. Non-vacuity

Two checks, in increasing strength.  The first is arithmetic: the parameter constraints of
`thm:speedyconductance` — the sandwich `Bₙ ⊆ K ⊆ 4σ√n Bₙ`, the step bound `δ ≤ σ/(8√n)`, the
paper's `d = min{δ ln 2/√n, σ/(16√n)}`, the `densDist_le_one` cap `4(d/σ)√n ≤ 1` and the
threshold `4(d/σ)√n ≤ 1/4` that `cor:overlap` supplies — are simultaneously satisfiable, at
parameters where the certified conductance is strictly positive.  The second *applies* the
theorem to a concrete kernel and measure, discharging **every** hypothesis, `hoverlap` and
`hiso` included. -/

/-- **The parameter constraints are simultaneously satisfiable.**  At `n = 4`, `σ = 1`,
`δ = 1/16`:

* `δ ≤ σ/(8√n)` (with equality), so the step bound is attained;
* `1 ≤ 4σ√n = 8`, so `Bₙ ⊆ K ⊆ 4σ√n Bₙ` is a satisfiable sandwich (it is `B₄ ⊆ K ⊆ 8B₄`);
* the paper's `d = min{δ ln 2/√n, σ/(16√n)}` equals its **first** term `δ ln 2/√n = ln 2/32`,
  so the corrected cap of discrepancy (iii) never binds;
* `4(d/σ)√n = ln 2/4 ≈ 0.173 ≤ 1/4`, hence also `≤ 1`, so `thm:iso`'s density branch is
  *inside* the region `Arlib.densDist_le_one` allows and is not vacuous;
* the certified conductance `δ ln 2/(640σ√n) = ln 2/20480 > 0`. -/
theorem speedyGaussian_params_satisfiable :
    ∃ (n : ℕ) (σ δ d : ℝ), 2 ≤ n ∧ 0 < σ ∧ 0 < δ ∧
      δ ≤ σ / (8 * Real.sqrt n) ∧
      1 ≤ 4 * σ * Real.sqrt n ∧
      d = min (δ * Real.log 2 / Real.sqrt n) (σ / (16 * Real.sqrt n)) ∧
      d = δ * Real.log 2 / Real.sqrt n ∧
      4 * (d / σ) * Real.sqrt n ≤ 1 / 4 ∧
      4 * (d / σ) * Real.sqrt n ≤ 1 ∧
      0 < δ * Real.log 2 / (640 * σ * Real.sqrt n) := by
  have hs : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  refine ⟨4, 1, 1 / 16, Real.log 2 / 32, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hs]; norm_num
  · rw [hs]; norm_num
  · rw [hs, show (1 : ℝ) / 16 * Real.log 2 / 2 = Real.log 2 / 32 by ring,
      show (1 : ℝ) / (16 * 2) = 1 / 32 by norm_num, min_eq_left (by linarith)]
  · rw [hs]; ring
  · rw [hs, show (4 : ℝ) * (Real.log 2 / 32 / 1) * 2 = Real.log 2 / 4 by ring]
    linarith
  · rw [hs, show (4 : ℝ) * (Real.log 2 / 32 / 1) * 2 = Real.log 2 / 4 by ring]
    linarith
  · rw [hs, show (1 : ℝ) / 16 * Real.log 2 / (640 * 1 * 2) = Real.log 2 / 20480 by ring]
    linarith

/-- **Non-vacuity witness (`CLAUDE.md` §11) for `conductance_speedyGaussian_ge`.**

Every hypothesis of the theorem — including the two with content, `hoverlap` and `hiso` — is
satisfiable *simultaneously*, at parameters where the conclusion is a **strictly positive**
lower bound on a genuine conductance, not the trivial `0 ≤ …`.

The instance is `n = 4`, `σ = 1`, `δ = 1/16` (so `δ = σ/(8√n)` exactly), `K = ℝ⁴`, `h` the
indicator of the ball `B = B(0, 1/128)`, `π` the uniform measure on `B`, and `P` the instantly
mixing kernel `P_x = π`.

* `hoverlap` holds because `P_u(Tᶜ) + P_v(T) = π(Tᶜ) + π(T) = 1 ≥ 1/20`.
* `hiso` holds because `B` has diameter `1/64`, strictly less than
  `d/ln 2 = δ/√n = 1/32`, while `h` is *constant* on `B`, so `d_h ≡ 0` there and the density
  branch `d_h ≥ ln 2/4` also fails.  Hence `S₁` and `S₂` cannot both meet `B`, one of
  `∫_{S₁} h`, `∫_{S₂} h` vanishes, and `thm:iso`'s left-hand side is `0`.  Note that this is
  a genuine verification of the hypothesis at these data, *not* a vacuous one: the separation
  hypothesis of `hiso` is satisfiable here (take `S₂ = ∅`).

The point of the second bullet is exactly the vacuity risk: `hiso` is an unproved universally
quantified statement, and a witness that merely asserted it would certify nothing.  Here it is
*proved* at the instance. -/
theorem exists_conductance_speedyGaussian_pos :
    ∃ (P : Kernel (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 4)))
      (pi : Measure (EuclideanSpace ℝ (Fin 4))),
      IsProbabilityMeasure pi ∧ IsMarkovKernel P ∧
      0 < ENNReal.ofReal (Real.log 2 / 20480) ∧
      ENNReal.ofReal (Real.log 2 / 20480) ≤ conductance P pi := by
  classical
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  set B : Set (EuclideanSpace ℝ (Fin 4)) := Metric.ball 0 (1 / 128) with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  set h : EuclideanSpace ℝ (Fin 4) → ℝ := Set.indicator B (fun _ => (1 : ℝ)) with hhdef
  set pi : Measure (EuclideanSpace ℝ (Fin 4)) := Arlib.uniformOn volume B with hpidef
  haveI hprob : IsProbabilityMeasure pi := Arlib.isProbabilityMeasure_uniformOn volume hB0 hBtop
  have hh0 : ∀ x, 0 ≤ h x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hint : ∀ A : Set (EuclideanSpace ℝ (Fin 4)),
      (∫ x in A, h x) = (volume (A ∩ B)).toReal := by
    intro A
    rw [hhdef, setIntegral_indicator hBm, setIntegral_const, smul_eq_mul, mul_one]
    exact measureReal_def _ _
  have hinttot : (∫ x, h x) = (volume B).toReal := by
    rw [← setIntegral_univ, hint, Set.univ_inter]
  have hmass : 0 < ∫ x, h x := by
    rw [hinttot]
    exact ENNReal.toReal_pos hB0 hBtop
  have hpiA : ∀ A : Set (EuclideanSpace ℝ (Fin 4)), MeasurableSet A →
      pi A = ENNReal.ofReal (∫ x in A, h x) / ENNReal.ofReal (∫ x, h x) := by
    intro A hA
    rw [hpidef, Arlib.uniformOn_apply volume hBm hA, hint, hinttot,
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top hBtop (measure_mono Set.inter_subset_right)),
      ENNReal.ofReal_toReal hBtop]
  -- `cor:overlap` at the instantly mixing kernel: the two one-step masses already sum to `1`
  have hoverlap : ∀ T : Set (EuclideanSpace ℝ (Fin 4)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin 4), u ∈ T → u ∈ (Set.univ : Set _) →
      v ∈ (Set.univ : Set _) → v ∉ T →
      ‖u - v‖ < (1 / 16 : ℝ) / Real.sqrt ((4 : ℕ) : ℝ) → densDist h u v < 1 / 4 →
      1 ≤ 20 * (Kernel.const (EuclideanSpace ℝ (Fin 4)) pi u Tᶜ
        + Kernel.const (EuclideanSpace ℝ (Fin 4)) pi v T) := by
    intro T hT u v _ _ _ _ _ _
    rw [Kernel.const_apply, Kernel.const_apply, add_comm, measure_add_measure_compl hT,
      measure_univ]
    norm_num
  -- `thm:iso` at the instance: `S₁` and `S₂` cannot both meet the tiny ball `B`
  have hisoW : ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin 4)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        (1 / 16 : ℝ) * Real.log 2 / Real.sqrt ((4 : ℕ) : ℝ) / Real.log 2 ≤ ‖u - v‖ ∨
          4 * ((1 / 16 : ℝ) * Real.log 2 / Real.sqrt ((4 : ℕ) : ℝ) / 1)
              * Real.sqrt ((4 : ℕ) : ℝ) ≤ densDist h u v) →
      (1 / 16 : ℝ) * Real.log 2 / Real.sqrt ((4 : ℕ) : ℝ) / 1
          * ((∫ x in S₁, h x) * ∫ x in S₂, h x)
        ≤ (∫ x, h x) * ∫ x in S₃, h x := by
    intro S₁ S₂ S₃ _ _ _ _ hsep
    have hMnn : 0 ≤ ∫ x, h x := integral_nonneg hh0
    have hnn3 : 0 ≤ ∫ x in S₃, h x := integral_nonneg hh0
    have hkey : (∫ x in S₁, h x) = 0 ∨ (∫ x in S₂, h x) = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hk1, hk2⟩ := hcon
      have h1' : 0 < ∫ x in S₁, h x := lt_of_le_of_ne (integral_nonneg hh0) (Ne.symm hk1)
      have h2' : 0 < ∫ x in S₂, h x := lt_of_le_of_ne (integral_nonneg hh0) (Ne.symm hk2)
      have hne : ∀ A : Set (EuclideanSpace ℝ (Fin 4)), 0 < (∫ x in A, h x) →
          (A ∩ B).Nonempty := by
        intro A hA
        rw [hint] at hA
        by_contra hc
        rw [Set.not_nonempty_iff_eq_empty] at hc
        rw [hc] at hA
        simp at hA
      obtain ⟨u, huS, huB⟩ := hne S₁ h1'
      obtain ⟨v, hvS, hvB⟩ := hne S₂ h2'
      have hnorm : ‖u - v‖ < 1 / 64 := by
        have hu : ‖u‖ < 1 / 128 := by rwa [hBdef, mem_ball_zero_iff] at huB
        have hv : ‖v‖ < 1 / 128 := by rwa [hBdef, mem_ball_zero_iff] at hvB
        calc ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
          _ < 1 / 128 + 1 / 128 := by linarith
          _ = 1 / 64 := by norm_num
      have hdd : densDist h u v = 0 := by
        simp only [densDist, hhdef, Set.indicator_of_mem huB, Set.indicator_of_mem hvB]
        norm_num
      rcases hsep u huS v hvS with hbr | hbr
      · rw [hs, show (1 : ℝ) / 16 * Real.log 2 / 2 / Real.log 2 = 1 / 32 by
          field_simp; norm_num] at hbr
        linarith
      · rw [hs, hdd,
          show (4 : ℝ) * ((1 : ℝ) / 16 * Real.log 2 / 2 / 1) * 2 = Real.log 2 / 4 by ring] at hbr
        linarith
    rcases hkey with hk | hk
    · rw [hk, zero_mul, mul_zero]
      exact mul_nonneg hMnn hnn3
    · rw [hk, mul_zero, mul_zero]
      exact mul_nonneg hMnn hnn3
  refine ⟨Kernel.const _ pi, pi, hprob, inferInstance, ?_, ?_⟩
  · rw [ENNReal.ofReal_pos]
    linarith
  · rw [show Real.log 2 / 20480
        = (1 / 16 : ℝ) * Real.log 2 / (640 * 1 * Real.sqrt ((4 : ℕ) : ℝ)) by rw [hs]; ring]
    exact conductance_speedyGaussian_ge (n := 4) (σ := 1) (δ := 1 / 16) (by norm_num)
      (by norm_num) (by norm_num) (by rw [hs]; norm_num) hh0 hmass
      (K := Set.univ) MeasurableSet.univ _ pi hpiA (isReversible_const pi) (by simp)
      hoverlap hisoW

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.two_mul_log_two_le_sqrt_natCast
#print axioms Arlib.MarkovChains.four_mul_isoStep_div_sigma_le_quarter
#print axioms Arlib.MarkovChains.isoStep_conductance_le_inv_160
#print axioms Arlib.MarkovChains.ofReal_div_mul_div_le
#print axioms Arlib.MarkovChains.measure_sdiff_add_measure_sdiff_le_flow
#print axioms Arlib.MarkovChains.measure_le_flow_of_le_two_mul

#print axioms Arlib.MarkovChains.conductance_speedyGaussian_ge

#print axioms Arlib.MarkovChains.speedyGaussian_params_satisfiable
#print axioms Arlib.MarkovChains.exists_conductance_speedyGaussian_pos
