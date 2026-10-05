/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.HitAndRunStep
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.CrossRatio
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalkConductance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.TV

/-!
# Theorem 4.2 of Lovász–Vempala: the conductance of hit-and-run

> L. Lovász and S. Vempala, *Hit-and-Run from a Corner*, STOC 2004 / SIAM J. Comput. 35
> (2006) 985–1005, `https://faculty.cc.gatech.edu/~vempala/papers/start.pdf`, §4.

> **Theorem 4.2.** Let `K` be a convex body in `ℝⁿ` of diameter `D`, containing a unit
> ball.  Then the conductance of hit-and-run in `K` is at least `1/(2²⁴·n·D)`.

Formally, `Arlib.MarkovChains.conductance_hitAndRun_ge`:

    ENNReal.ofReal (1 / (2 ^ 27 * n * D)) ≤ conductance (hitAndRun K) (uniformOn volume K)

with `conductance` the genuine infimum of `Arlib/MarkovChains/Continuous/Conductance.lean`
and `hitAndRun` the kernel of `Arlib/MarkovChains/Continuous/HitAndRun.lean`.

**`2²⁷`, not the paper's `2²⁴`, and the reason is a constant and nothing else.**  Lemma 3.3
is proved in this repository (`Arlib.lem33_sqrt`) at `10·t√n/2r` rather than the paper's
`t√n/2r`, so Lemma 3.4 reads `∫_K s ≥ ((1−α)/(10√n))·vol K`; that factor `10` propagates
verbatim to the headline, giving `1/(122880000·n·D)`, and `122880000 > 2²⁴ = 16777216`.  The
factor `10` is a constant-factor loss in the exponential-envelope majorant that
`KLS97Sharp.lean`'s route uses in place of the Gaussian — **not** an error in KLS 1997, whose
`C = 1` is consistent with everything proved here.  The order in `n` and `D` is the paper's.

This file assembles that theorem — `Arlib.MarkovChains.conductance_hitAndRun_ge` — around
**two inline `∀`-hypotheses**, and proves everything else.  The two are *not* on the
same footing, and the difference is the point of this file:

## 1. `hIso` — the open gap, **and a correction to the paper**

`hIso` is the paper's **Theorem 2.1**, the weighted isoperimetric inequality, specialised
to the uniform density (which is all Theorem 4.2 consumes):

> Let `S₁, S₂, S₃` partition the convex body `K` and let `h : K → ℝ₊` satisfy
> `h(x) ≤ (1/3)·min(1, d_K(u,v))` for every `u ∈ S₁`, `v ∈ S₂` and every `x` on the chord
> of `K` through `u` and `v`, **and `h ≤ 1/3` on all of `K`**.  Then
> `π(S₃) ≥ E_π(h)·min(π S₁, π S₂)`.

### The emphasised clause is not in the paper, and Theorem 2.1 is FALSE without it

The printed hypothesis constrains `h` only on the union of the chords through cross pairs,
while the conclusion integrates `h` over all of `K`; for `n ≥ 2` that union can miss a set
of positive measure, on which `h` is unconstrained.  `Arlib.not_hIso_two`
(`Arlib/Convexity/LovaszVempalaIsoFalse.lean`) is the **negation of the binder as it was
previously written here**, machine-checked at `n = 2` and `K = [0,4]²`, with
`T₁ = [0,1/2]²`, `T₂ = [7/2,4]×[0,1/2]` and `h = 1000·1_{[0,4]×[4/3,4]}`: no cross chord
rises above height `7/6`, so `h` vanishes on every one of them, yet
`E_π(h)·min(π T₁, π T₂) = 125/12 > 1 ≥ π(K ∖ T₁ ∖ T₂)`.  `Arlib.cexK_hitAndRun_hypotheses`
checks that this `K` satisfies *every other* hypothesis of `conductance_hitAndRun_ge`, so the
old binder made this theorem **vacuous at that instance**.

The repair costs the argument nothing: the paper's own §4 application verifies `h ≤ 1/3`
("clearly"), and that step is `Arlib.MarkovChains.weight_le_third` here — in the stronger
form `h ≤ 1/(24√n)`.  It is discharged at the use site inside
`conductance_hitAndRun_ge_of_tv`, so no caller has to supply it.
`Arlib.cexH_not_le_third` confirms the new clause is exactly what kills the counterexample.
`Arlib.not_hIso_two_measurable` further shows that adding `Measurable h` would **not** be a
repair — the counterexample weight is measurable — which is why no measurability binder was
added; the repo has no measurability lemma for `Arlib.stepRadius` to discharge one with.

### What remains open, and it is not Borsuk–Ulam

Lovász–Vempala prove Theorem 2.1 by a single invocation of the Localization Lemma
(Kannan–Lovász–Simonovits 1995, Corollary 2.4) on a *signed* pair of integrands.  Earlier
versions of this docstring said the signed case "is where Borsuk–Ulam re-enters" and that
Borsuk–Ulam is absent from Mathlib; **that is stale**.  `Arlib.exists_flat_cut_zero_pos`
(`Arlib/Convexity/LocalizationAssembly.lean:370`) takes **arbitrary signed** integrands
`g₁ g₂ : E → ℝ` — its only hypotheses on them are `IntegrableOn`, `∫_C g₁ = 0` and
`0 < ∫_C g₂` — and delivers a cut with `∫ g₁ = 0` and `0 < ∫ g₂` on one side.  With the
equality-refined form only **one** integrand is ever bisected, by a one-parameter
intermediate value theorem (`Arlib.exists_pencil_bisecting`); the other needs no bisection
because its two masses sum to something positive.  No Borsuk–Ulam is used anywhere.

Everything in §2 of the paper except that invocation is now proved, in
`Arlib/Convexity/LovaszVempalaIso.lean`: `Arlib.oneDim_crossRatio_partition` (the
one-dimensional cross-ratio inequality for measurable partitions), `Arlib.needle_iso` (the
repaired one-dimensional Theorem 2.1) and `Arlib.needle_iso_of_chord` (Theorem 2.1 on a
needle inside `K`, unconditional).  `Arlib.thm21_of_localization` is Theorem 2.1 for the
uniform density with the Localization Lemma as its single binder.

The residuals are the two that `Arlib/Convexity/LocalizationAssembly.lean` classifies as
open, and both moved today:

* **(C) lower semicontinuity** — `Arlib/Convexity/LocalizationLSC.lean` runs the needle with
  `g₂` bounded *lower semicontinuous*.  This is only half of what Theorem 2.1 needs: the
  `g₁` slot carries an **equality** and `g₁ = 1_{T₁} − A·1_K` is merely measurable, which
  that file's own boundary discussion shows is not reachable (a needle is a null set, and the
  equality does not transfer even for open `S`).
* **(F) the Euclidean transport and nondegeneracy** — closed in
  `Arlib/Convexity/LocalizationTransport.lean`
  (`Arlib.exists_needleIntegral_eq_zero_and_pos_of_compact_chain_euclidean`, via
  `PiLp.volume_preserving_toLp`), with nondegeneracy closed modulo one explicit `hsep`.

`hIso` is written out **inline, as a `∀`-hypothesis of the theorem that consumes it** — not a
named `Prop`, not a `structure` field, not a `class`.  A reader of
`conductance_hitAndRun_ge`'s type sees the inequality in full.  Compare
`../gaussian-cooling-vempala/lean/Isoperimetry.lean`, which "has" isoperimetry only through
an `IsoInput`/`OneDimIso` predicate that assumes its own conclusion; that is exactly the
mistake this file refuses to make — and the counterexample above is why writing the binder
out in full matters: it is what made the error findable.

## 2. `hLem41` — a placeholder for work in flight, not a gap

`hLem41` is **temporary**, and is being proved concurrently in this same repository.  It is
threaded here in the same inline style purely so that this file can be built and audited
before it lands; when it does, it is discharged by a single application.

`hLem41` is the paper's **Lemma 4.1**, the one-step overlap bound: two points that are close
in cross-ratio distance *and* close relative to their median step lengths have overlapping
one-step distributions.  It is being proved in
`Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean`.

It is not an obstruction of the kind `hIso` is: it is ordinary (if laborious) geometry that
the surrounding development already knows how to do.  As of writing that concurrent file does
not discharge it *at the paper's constant*, and the difference is recorded here rather than
hidden: `tvLe_hitAndRun_lemma41` obtains `1 − 1/2880` rather than the paper's `1 − 1/500`
(its cap constant is `1/2`, not the paper's erroneous `1/6`), and it hypothesises
`|u−v| < (2/√n)·F(u)` rather than the paper's `max{F(u),F(v)}` — the latter follows by
symmetry, since `TVLe` and `crossRatioDist` are symmetric.  **This is why the theorem below
is stated twice**: once parametrically in the Lemma 4.1 loss
(`conductance_hitAndRun_ge_of_tv`, giving `lam/(245760·n·D)` from `d_TV ≤ 1 − lam`), and once
at the paper's `lam = 1/500` (`conductance_hitAndRun_ge`, giving `1/(2²⁷·n·D)`).  At
`lam = 1/2880` the same theorem gives `1/(707788800·n·D)`, i.e. roughly `1/2³⁰·n·D`.

## 3. `hLem33` — discharged; no longer a hypothesis of this file

The paper's **Lemma 3.3** (= Corollary 4.6 of Kannan–Lovász–Simonovits 1997), quoted without
proof by Lovász–Vempala, **is proved in this repository**, as
`Arlib.lintegral_volume_closedBall_sdiff_le_sqrt` in `Arlib/Convexity/KLS97Sharp.lean` (its
inradius-`1` specialisation being `Arlib.lem33_sqrt`).  It used to be threaded through this
file as an inline `∀`-hypothesis `hLem33`, because `Arlib.lintegral_stepRadius_ge` carried one
of exactly that shape; `StepLength.lean` now discharges it internally from
`hball : closedBall z 1 ⊆ K` — the paper's own "Suppose `K` contains a unit ball" — and **no
`hLem33` binder survives anywhere in this file.**

What is proved is the `10√n` form, not the paper's `√n`.  That is a constant-factor loss in
the majorant of the proof route in `KLS97Sharp.lean` (an exponential envelope `e^{2−λh}` in
place of the Gaussian, plus `(1+x)ⁿ − 1 ≤ nx·e^{nx}`), **not** an error in KLS97.  The order
is `√n`, as in the paper; only the absolute constant differs, and the whole cost downstream is
the factor `10` in the headline recorded at the top of this docstring.

## What is proved here

Everything else in §4:

* `Arlib.MarkovChains.stepRadius_le_two_mul_diam` — `s_α(x) ≤ 2·diam K` for `α ≥ 1/2`.
  This is the paper's unargued "clearly `h(x) ≤ 1/3`".
* `Arlib.MarkovChains.stepRadius_le_of_chord` — **the chain of §4**, in the chord
  coordinate:

      s(x) ≤ (|x−p|/|u−p|)·s(u) ≤ 32(|q−p|/|u−p|)·F(u) ≤ 16√n·|u−v|·(|q−p|/|u−p|)
           = 16·d_K(u,v)·√n·|q−v| ≤ 16·d_K(u,v)·D√n,

  for every `x` on the chord through `u` and `v`.  It uses Lemma 3.1 (concavity, as
  `Arlib.theta_mul_stepRadius_le`), Lemma 3.2 (`Arlib.stepRadius_le_medianStep`), and the
  hypothesis `|u−v| ≥ (2/√n)·max{F(u),F(v)}` that the failure of Lemma 4.1 supplies.  The
  paper writes only the case "`x` between `u` and `q`" and says "e.g."; both cases are
  proved here, the second by the mirror-image argument through `v` and `q`.
* `Arlib.MarkovChains.weight_le_of_chord` — the verification of Theorem 2.1's hypothesis
  for `h(x) = s(x)/(48·D·√n)`, in both branches of the dichotomy (`d_K(u,v) ≥ 1/8`, or the
  separation bound above).
* `Arlib.MarkovChains.one_le_diam_of_unitBall` — `diam K ≥ 1` for a body with inradius `1`.
* `Arlib.MarkovChains.conductance_hitAndRun_ge_of_tv` — **Theorem 4.2, parametric in the
  Lemma 4.1 loss**: `d_TV ≤ 1 − lam` gives `Φ ≥ lam/(245760·n·D)`.
* `Arlib.MarkovChains.conductance_hitAndRun_ge` — **Theorem 4.2**, at `lam = 1/500`:
  `Φ ≥ 1/(2²⁷·n·D)`.

## Reused rather than rebuilt

* `Arlib.MarkovChains.conductance` (`Conductance.lean`) — the genuine infimum.
* `Arlib.MarkovChains.hitAndRun`, `isReversible_hitAndRun` (`HitAndRun.lean`).
* `Arlib.stepRadius_concaveOn`, `theta_mul_stepRadius_le`, `lintegral_stepRadius_ge`
  (`StepLength.lean` — Lemmas 3.1 and 3.4).
* `Arlib.stepRadius_le_medianStep`, `medianStep` (`HitAndRunStep.lean` — Lemma 3.2).
* `Arlib.crossRatioDist` and the chord coordinate (`CrossRatio.lean`).
* `Arlib.MarkovChains.mul_measure_add_measure_le_mul_flow` (`BallWalkConductance.lean`) —
  the three-way-partition flow accounting, stated there for an arbitrary reversible Markov
  kernel on an arbitrary measurable space.  It is exactly the accounting §4 needs.

## Constants, and where they differ from the paper

The headline constant is `1/(2²⁷·n·D)` where the paper writes `1/(2²⁴·n·D)`.  **The entire
difference is the factor `10` in the proved Lemma 3.3**; every other step of the bookkeeping
here is the paper's or slightly better than it:

| quantity | paper | here |
|---|---|---|
| Lemma 3.3 | `t√n/2r` | `10·t√n/2r` (proved, `KLS97Sharp.lean`) |
| `∫_K s / vol K` | `> 1/4000·nD` after `1/(48D√n)` | `≥ 1/(30720·n·D)` (exact `48·64·10`) |
| escape flow | `≥ (1/2000)·vol(S₃')` | same |
| final | `1/2²⁴·nD` | `1/(122880000·n·D) ≥ 1/2²⁷·nD` |
| general | — | `lam/(245760·n·D)` from `d_TV ≤ 1 − lam` |

The paper reaches `2²⁴` as `2²³` times a factor `2` for `vol(Sᵢ') ≥ vol(Sᵢ)/2`; here the
same factor `2` appears one step earlier, as `π(S) ≤ 2·min(π S₁', π S₂')`, and the
arithmetic lands at `500·245760 = 122880000 ≤ 2²⁷ = 134217728`.  Absent the factor `10` the
same route would land at `12288000 ≤ 2²⁴`, i.e. exactly the paper's statement; that factor is
a constant-factor loss in a majorant, not a discrepancy with KLS97 (see §3 above).

## Two places where the formalisation is more careful than the paper

1. **Interior points.**  `S₁'` and `S₂'` are cut down to `interior K`.  Two of the inputs
   genuinely need it: at a boundary point `u` the chord endpoint `p` *is* `u`, so the
   cross-ratio distance `d_K(u,v) = |u−v||p−q|/(|p−u||v−q|)` divides by zero (Lean returns
   the junk value `0`, which would make Theorem 2.1's hypothesis unsatisfiable), and
   Lemma 3.2 needs `hitAndRunProposal K u univ = 1`, which
   `Arlib.hitAndRunProposal_univ_eq_one_of_mem_interior` supplies only at an interior
   point.  Nothing is lost: `Convex.addHaar_frontier` gives `vol(K \ interior K) = 0`.
2. **`h(x) ≤ 1/3`.**  The paper says "clearly".  It is `s(x) ≤ 2·diam K`, proved here from
   `α ≥ 1/2` and `K ⊆ closedBall x (diam K)`; the resulting `h(x) ≤ 1/(24√n)` is what makes
   *both* branches of the dichotomy go through, including the `d_K(u,v) ≥ 1/8` branch where
   the paper's "trivial" needs `1/(24√n) ≤ 1/24`.

## Scope

There is no mixing-time statement here.  `Arlib.MarkovChains.mixesWithin_of_conductance`
(`L2Mixing.lean`) is what would consume this bound, and it additionally needs a
nonnegative-spectrum hypothesis, which for hit-and-run is a separate question (the lazy
version of `BallWalkConductance.lean` is the standard fix).  This file stops at the
conductance, which is what Theorem 4.2 is.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. `s_α(x) ≤ 2·diam K` — the paper's "clearly `h(x) ≤ 1/3`" -/

/-- **The step radius never exceeds twice the diameter.**

If `t` is admissible at `x ∈ K` then `α·vol(tB) ≤ vol(K ∩ (x + tB)) ≤ vol K ≤ vol(Δ·B)`
with `Δ = diam K`, because `K ⊆ x + Δ·B`.  Cancelling `vol(B)` gives `α·tⁿ ≤ Δⁿ`, and with
`α ≥ 1/2` and `n ≥ 1` this is `tⁿ ≤ 2·Δⁿ ≤ (2Δ)ⁿ`, i.e. `t ≤ 2Δ`.

This is what the paper asserts without argument when it writes "clearly `h(x) ≤ 1/3`" for
`h(x) = s(x)/(48·D·√n)`. -/
theorem stepRadius_le_two_mul_diam (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) {α : ℝ} (hα : 1 / 2 ≤ α)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) :
    stepRadius K α x ≤ 2 * Metric.diam K := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hΔ : (0 : ℝ) ≤ Metric.diam K := Metric.diam_nonneg
  set Vb : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hVbdef
  have hVb0 : Vb ≠ 0 := volume_euclideanUnitBall_ne_zero
  have hVbtop : Vb ≠ ⊤ := measure_ball_lt_top.ne
  have hVbpos : 0 < Vb.toReal := ENNReal.toReal_pos hVb0 hVbtop
  refine csSup_le (stepRadiusSet_nonempty hn K α x) ?_
  rintro t ⟨ht0, ht⟩
  have hsub : K ⊆ Metric.closedBall x (Metric.diam K) := by
    intro y hy
    rw [Metric.mem_closedBall]
    exact Metric.dist_le_diam_of_mem hKb hy hx
  have key : ENNReal.ofReal (α * t ^ n) * Vb
      ≤ ENNReal.ofReal (Metric.diam K ^ n) * Vb := by
    calc ENNReal.ofReal (α * t ^ n) * Vb
        = ENNReal.ofReal α * volume (Metric.closedBall x t) := by
          rw [volume_closedBall_euclidean ht0, ENNReal.ofReal_mul hα0.le,
            ENNReal.ofReal_pow ht0, ← hVbdef, mul_assoc]
      _ ≤ volume (K ∩ Metric.closedBall x t) := ht
      _ ≤ volume (Metric.closedBall x (Metric.diam K)) :=
          (measure_mono Set.inter_subset_left).trans (measure_mono hsub)
      _ = ENNReal.ofReal (Metric.diam K ^ n) * Vb := by
          rw [volume_closedBall_euclidean hΔ, ENNReal.ofReal_pow hΔ, ← hVbdef]
  have hfin : ENNReal.ofReal (Metric.diam K ^ n) * Vb ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVbtop
  have hreal : α * t ^ n * Vb.toReal ≤ Metric.diam K ^ n * Vb.toReal := by
    have h := ENNReal.toReal_mono hfin key
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at h
  have hkey : α * t ^ n ≤ Metric.diam K ^ n := le_of_mul_le_mul_right hreal hVbpos
  have h2n : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn)
  have hpow : t ^ n ≤ (2 * Metric.diam K) ^ n := by
    have hd : (0 : ℝ) ≤ Metric.diam K ^ n := by positivity
    have h1 : t ^ n ≤ 2 * Metric.diam K ^ n := by nlinarith [pow_nonneg ht0 n]
    calc t ^ n ≤ 2 * Metric.diam K ^ n := h1
      _ ≤ 2 ^ n * Metric.diam K ^ n := by nlinarith
      _ = (2 * Metric.diam K) ^ n := (mul_pow 2 _ n).symm
  exact (pow_le_pow_iff_left₀ ht0 (by positivity) hn).1 hpow

/-- **The paper's unargued "clearly `h(x) ≤ 1/3`", as a standalone bound.**

For `h(x) = s_α(x)/(48·D·√n)` and any `x ∈ K`, `s_α(x) ≤ 2·diam K ≤ 2D`
(`Arlib.MarkovChains.stepRadius_le_two_mul_diam`) and `48·D·√n ≥ 48·D`, so
`h(x) ≤ 2D/(48D√n) = 1/(24√n) ≤ 1/24 ≤ 1/3`.

It appears inside `Arlib.MarkovChains.weight_le_of_chord` as an intermediate step, but it is
needed on its own now: the `hIso` binder of the theorems below carries `∀ x ∈ K, h x ≤ 1/3`
as an explicit hypothesis, because **without it Theorem 2.1 is false** — see
`Arlib.not_hIso_two` (`Arlib/Convexity/LovaszVempalaIsoFalse.lean`).  This lemma is what
discharges that hypothesis at the use site, so the repair costs the argument nothing. -/
theorem weight_le_third (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) {α : ℝ} (hα : 1 / 2 ≤ α)
    {D : ℝ} (hD : Metric.diam K ≤ D) (hD0 : 0 < D)
    {x : EuclideanSpace ℝ (Fin n)} (hxK : x ∈ K) :
    stepRadius K α x / (48 * D * Real.sqrt n) ≤ 1 / 3 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hc0 : (0 : ℝ) < 48 * D * Real.sqrt n := by positivity
  have hsmall : stepRadius K α x ≤ 2 * D := by
    have h := stepRadius_le_two_mul_diam hn hKb hα hxK
    linarith
  rw [div_le_iff₀ hc0]
  nlinarith [mul_nonneg hD0.le (sub_nonneg.mpr hsq1)]

/-! ## 2. The chain of §4 -/

/-- **The chain of §4 of Lovász–Vempala**, in the chord coordinate.

Let `u, v` be interior points of a convex body `K`, and suppose the separation
`|u−v| ≥ (2/√n)·max{F(u), F(v)}` holds — i.e. `F(u), F(v) ≤ (√n/2)·|u−v|`, which is what
the *failure* of the paper's Lemma 4.1 supplies.  Then for **every** point `x` on the chord
of `K` through `u` and `v`,

    s_α(x) ≤ 16·√n·d_K(u,v)·diam K.

The paper's own chain, with `p, u, v, q` in order along the chord, is

    s(x) ≤ (|x−p|/|u−p|)·s(u) ≤ 32(|q−p|/|u−p|)·F(u) ≤ 16√n·|u−v|·(|q−p|/|u−p|)
         = 16·d_K(u,v)·√n·|q−v| ≤ 16·d_K(u,v)·D√n,

and it is run here in the chord parameter: with `a = chordLow < 0`, `b = chordHigh > 1` and
`L = |u−v|`, one has `|x−p| = (t−a)L`, `|u−p| = (−a)L`, `|q−p| = (b−a)L`, `|v−q| = (b−1)L`
and `d_K(u,v) = (b−a)/((−a)(b−1))`, so every ratio becomes a scalar identity.

The first `≤` is Lemma 3.1 (`Arlib.theta_mul_stepRadius_le`) with
`θ = |u−p|/|x−p| = (−a)/(t−a)`, the second is Lemma 3.2
(`Arlib.stepRadius_le_medianStep`), the third is the separation hypothesis.

The paper writes only "let e.g. `x` be between `u` and `q`"; the mirror case `x` between
`p` and `u` is proved here too, by running the same argument through `v`, `q` and `F(v)`
(the parameter `θ' = (b−1)/(b−t)`), which is why both `hFu` and `hFv` appear. -/
theorem stepRadius_le_of_chord (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (hKfin : volume K ≠ ⊤)
    {α : ℝ} (hα : 63 / 64 ≤ α) (hα1 : α ≤ 1)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ interior K) (hv : v ∈ interior K) (huv : u ≠ v)
    (hmu : hitAndRunProposal K u Set.univ = 1) (hmv : hitAndRunProposal K v Set.univ = 1)
    (hFu : medianStep K u ≤ Real.sqrt n / 2 * dist u v)
    (hFv : medianStep K v ≤ Real.sqrt n / 2 * dist u v)
    {x : EuclideanSpace ℝ (Fin n)} (hxK : x ∈ K) {t : ℝ}
    (hxt : x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) :
    stepRadius K α x ≤ 16 * Real.sqrt n * crossRatioDist K u v * Metric.diam K := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have huK : u ∈ K := interior_subset hu
  have hvK : v ∈ K := interior_subset hv
  have hL : 0 < dist u v := dist_pos.mpr huv
  set a : ℝ := chordLow K u v with hadef
  set b : ℝ := chordHigh K u v with hbdef
  have ha : a < 0 := chordLow_neg_of_mem_interior hKb huv hu
  have hb : 1 < b := one_lt_chordHigh_of_mem_interior hKb huv hv
  have hane : a ≠ 0 := ne_of_lt ha
  have hb1ne : b - 1 ≠ 0 := ne_of_gt (by linarith)
  have hp : chordStart K u v ∈ K := chordStart_mem hKc hKcl hKb huv huK hvK
  have hq : chordEnd K u v ∈ K := chordEnd_mem hKc hKcl hKb huv huK hvK
  have htmem : t ∈ Set.Icc a b := by
    rw [hadef, hbdef, ← chordParam_eq_Icc hKc hKcl hKb huv huK]
    exact (hxt ▸ hxK : (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t ∈ K)
  have hdK : crossRatioDist K u v = (b - a) / (-a * (b - 1)) :=
    crossRatioDist_eq_param hKb huv huK hvK
  have hdpos : 0 < crossRatioDist K u v := crossRatioDist_pos hKb huv huK hvK ha hb
  -- Lemma 3.2 plus the separation hypothesis at `u` and at `v`
  have hsu : stepRadius K α u ≤ 16 * Real.sqrt n * dist u v := by
    have h32 := stepRadius_le_medianStep hn hKc hKm huK hα hα1 hmu
    nlinarith [medianStep_nonneg K u]
  have hsv : stepRadius K α v ≤ 16 * Real.sqrt n * dist u v := by
    have h32 := stepRadius_le_medianStep hn hKc hKm hvK hα hα1 hmv
    nlinarith [medianStep_nonneg K v]
  have hx' : x = (1 - t) • u + t • v := by
    rw [hxt, AffineMap.lineMap_apply_module]
  have hpos16 : (0 : ℝ) ≤ 16 * Real.sqrt n * dist u v := by positivity
  rcases le_or_gt 0 t with ht0 | ht0
  · -- `x` lies between `u` and `q`: push down to `u` through `p`
    have hta : 0 < t - a := by linarith
    set θ : ℝ := -a / (t - a) with hθdef
    have hθpos : 0 < θ := div_pos (by linarith) hta
    have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hta]; linarith
    have hcoef : θ * t + (1 - θ) * a = 0 := by
      have h : θ * (t - a) = -a := div_mul_cancel₀ _ hta.ne'
      linear_combination h
    have hp' : chordStart K u v = (1 - a) • u + a • v := by
      rw [chordStart, ← hadef, AffineMap.lineMap_apply_module]
    have hcomb : θ • x + (1 - θ) • chordStart K u v = u := by
      rw [hx', hp']
      match_scalars
      · linear_combination -hcoef
      · linear_combination hcoef
    have hconc := theta_mul_stepRadius_le hn hKc hKm hKfin hα0 hp hxK hθpos.le hθ1
    rw [hcomb] at hconc
    have hcinv : θ * ((t - a) / -a) = 1 := by
      rw [hθdef]; field_simp [hane]
    have hc0 : (0 : ℝ) < (t - a) / -a := div_pos hta (by linarith)
    have h1 : stepRadius K α x ≤ (t - a) / -a * (16 * Real.sqrt n * dist u v) := by
      calc stepRadius K α x = (t - a) / -a * (θ * stepRadius K α x) := by
            rw [← mul_assoc, mul_comm ((t - a) / -a) θ, hcinv, one_mul]
        _ ≤ (t - a) / -a * (16 * Real.sqrt n * dist u v) :=
            mul_le_mul_of_nonneg_left (hconc.trans hsu) hc0.le
    have h2 : (t - a) / -a ≤ (b - a) / -a := by
      gcongr
      · linarith
      · exact htmem.2
    have h3 : (b - a) / -a = crossRatioDist K u v * (b - 1) := by
      rw [hdK]
      field_simp
    have h4 : (b - 1) * dist u v ≤ Metric.diam K := by
      have heq : dist v (chordEnd K u v) = (b - 1) * dist u v := by
        rw [chordEnd, ← hbdef, dist_lineMap_right,
          abs_of_nonpos (by linarith : (1 : ℝ) - b ≤ 0)]
        ring
      rw [← heq]
      exact Metric.dist_le_diam_of_mem hKb hvK hq
    calc stepRadius K α x ≤ (t - a) / -a * (16 * Real.sqrt n * dist u v) := h1
      _ ≤ (b - a) / -a * (16 * Real.sqrt n * dist u v) := by gcongr
      _ = 16 * Real.sqrt n * crossRatioDist K u v * ((b - 1) * dist u v) := by
          rw [h3]; ring
      _ ≤ 16 * Real.sqrt n * crossRatioDist K u v * Metric.diam K := by
          gcongr
  · -- `x` lies between `p` and `u`: push down to `v` through `q`
    have htb : 0 < b - t := by linarith
    set θ : ℝ := (b - 1) / (b - t) with hθdef
    have hθpos : 0 < θ := div_pos (by linarith) htb
    have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one htb]; linarith
    have hcoef : θ * t + (1 - θ) * b = 1 := by
      have h : θ * (b - t) = b - 1 := div_mul_cancel₀ _ htb.ne'
      linear_combination -h
    have hq' : chordEnd K u v = (1 - b) • u + b • v := by
      rw [chordEnd, ← hbdef, AffineMap.lineMap_apply_module]
    have hcomb : θ • x + (1 - θ) • chordEnd K u v = v := by
      rw [hx', hq']
      match_scalars
      · linear_combination -hcoef
      · linear_combination hcoef
    have hconc := theta_mul_stepRadius_le hn hKc hKm hKfin hα0 hq hxK hθpos.le hθ1
    rw [hcomb] at hconc
    have hcinv : θ * ((b - t) / (b - 1)) = 1 := by
      rw [hθdef]; field_simp [hb1ne]
    have hc0 : (0 : ℝ) < (b - t) / (b - 1) := div_pos htb (by linarith)
    have h1 : stepRadius K α x ≤ (b - t) / (b - 1) * (16 * Real.sqrt n * dist u v) := by
      calc stepRadius K α x = (b - t) / (b - 1) * (θ * stepRadius K α x) := by
            rw [← mul_assoc, mul_comm ((b - t) / (b - 1)) θ, hcinv, one_mul]
        _ ≤ (b - t) / (b - 1) * (16 * Real.sqrt n * dist u v) :=
            mul_le_mul_of_nonneg_left (hconc.trans hsv) hc0.le
    have h2 : (b - t) / (b - 1) ≤ (b - a) / (b - 1) := by
      gcongr
      linarith [htmem.1]
    have h3 : (b - a) / (b - 1) = crossRatioDist K u v * -a := by
      rw [hdK]
      field_simp
    have h4 : -a * dist u v ≤ Metric.diam K := by
      have heq : dist (chordStart K u v) u = -a * dist u v := by
        rw [chordStart, ← hadef, dist_lineMap_left, abs_of_nonpos ha.le]
      rw [← heq]
      exact Metric.dist_le_diam_of_mem hKb hp huK
    calc stepRadius K α x ≤ (b - t) / (b - 1) * (16 * Real.sqrt n * dist u v) := h1
      _ ≤ (b - a) / (b - 1) * (16 * Real.sqrt n * dist u v) := by gcongr
      _ = 16 * Real.sqrt n * crossRatioDist K u v * (-a * dist u v) := by
          rw [h3]; ring
      _ ≤ 16 * Real.sqrt n * crossRatioDist K u v * Metric.diam K := by
          gcongr

/-! ## 3. Theorem 2.1's hypothesis, verified for `h(x) = s(x)/(48·D·√n)` -/

/-- **The weight function of §4 satisfies Theorem 2.1's hypothesis.**

With `h(x) = s_α(x)/(48·D·√n)` and `α = 63/64`, for interior points `u ≠ v` of `K` and any
`x` on the chord of `K` through them,

    h(x) ≤ (1/3)·min(1, d_K(u,v)),

*provided* the dichotomy `hcase` holds: either `d_K(u,v) ≥ 1/8`, or the separation
`F(u), F(v) ≤ (√n/2)·|u−v|`.  That dichotomy is exactly what the failure of the paper's
Lemma 4.1 supplies at a pair of "deep" points.

Both branches also need `h(x) ≤ 1/3`, which the paper calls clear: it is
`h(x) ≤ 2·diam K/(48·D·√n) ≤ 1/(24√n) ≤ 1/24` from
`Arlib.MarkovChains.stepRadius_le_two_mul_diam`.  In the first branch that bound *is* the
whole argument, since `(1/3)·min(1, d_K) ≥ (1/3)·(1/8) = 1/24`. -/
theorem weight_le_of_chord (hn : n ≠ 0) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (hKfin : volume K ≠ ⊤)
    {α : ℝ} (hα : 63 / 64 ≤ α) (hα1 : α ≤ 1)
    {D : ℝ} (hD : Metric.diam K ≤ D) (hD0 : 0 < D)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ interior K) (hv : v ∈ interior K) (huv : u ≠ v)
    (hmu : hitAndRunProposal K u Set.univ = 1) (hmv : hitAndRunProposal K v Set.univ = 1)
    (hcase : 1 / 8 ≤ crossRatioDist K u v ∨
      (medianStep K u ≤ Real.sqrt n / 2 * dist u v ∧
        medianStep K v ≤ Real.sqrt n / 2 * dist u v))
    {x : EuclideanSpace ℝ (Fin n)} (hxK : x ∈ K) {t : ℝ}
    (hxt : x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) :
    stepRadius K α x / (48 * D * Real.sqrt n) ≤ min 1 (crossRatioDist K u v) / 3 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hc0 : (0 : ℝ) < 48 * D * Real.sqrt n := by positivity
  have hdnn : 0 ≤ crossRatioDist K u v :=
    crossRatioDist_nonneg hKb huv (interior_subset hu) (interior_subset hv)
  -- the "clearly `h(x) ≤ 1/3`" bound, quantified: `h(x) ≤ 1/24`
  have hsmall : stepRadius K α x ≤ 2 * D := by
    have h := stepRadius_le_two_mul_diam hn hKb (by linarith : (1 : ℝ) / 2 ≤ α) hxK
    linarith
  have h24 : stepRadius K α x / (48 * D * Real.sqrt n) ≤ 1 / 24 := by
    rw [div_le_iff₀ hc0]
    nlinarith [mul_nonneg hD0.le (sub_nonneg.mpr hsq1)]
  have hA1 : stepRadius K α x / (48 * D * Real.sqrt n) ≤ 1 / 3 := by linarith
  have hAd : stepRadius K α x / (48 * D * Real.sqrt n) ≤ crossRatioDist K u v / 3 := by
    rcases hcase with hc | ⟨hFu, hFv⟩
    · -- `d_K(u,v) ≥ 1/8`, so `d_K/3 ≥ 1/24`, and the "clearly" bound already suffices
      linarith
    · -- the separation branch: the chain of §4
      have hchain := stepRadius_le_of_chord hn hKc hKcl hKm hKb hKfin hα hα1 hu hv huv hmu hmv
        hFu hFv hxK hxt
      have hchain' : stepRadius K α x ≤ 16 * Real.sqrt n * crossRatioDist K u v * D := by
        refine hchain.trans ?_
        have hnn : (0 : ℝ) ≤ 16 * Real.sqrt n * crossRatioDist K u v := by positivity
        exact mul_le_mul_of_nonneg_left hD hnn
      rw [div_le_iff₀ hc0]
      calc stepRadius K α x ≤ 16 * Real.sqrt n * crossRatioDist K u v * D := hchain'
        _ = crossRatioDist K u v / 3 * (48 * D * Real.sqrt n) := by ring
  rcases le_total (1 : ℝ) (crossRatioDist K u v) with h | h
  · rw [min_eq_left h]; exact hA1
  · rw [min_eq_right h]; exact hAd

/-- **A body containing a unit ball has diameter at least `1`.**  Used only for
non-degeneracy: it is what makes the two constant comparisons of Theorem 4.2 go through. -/
theorem one_le_diam_of_unitBall (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKb : Bornology.IsBounded K) {z : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.closedBall z 1 ⊆ K) : (1 : ℝ) ≤ Metric.diam K := by
  set y : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) with hy
  have hyn : ‖y‖ = 1 := by rw [hy, PiLp.norm_single]; norm_num
  have hdist : dist z (z + y) = ‖y‖ := by
    rw [dist_eq_norm, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  have hzK : z ∈ K := hball (by simp)
  have hyK : z + y ∈ K := hball (by rw [Metric.mem_closedBall, dist_comm, hdist, hyn])
  rw [← hyn, ← hdist]
  exact Metric.dist_le_diam_of_mem hKb hzK hyK

/-! ## 4. Theorem 4.2 -/

/-- **Theorem 4.2 of Lovász–Vempala, parametric in the Lemma 4.1 loss.**  For a convex body
`K ⊆ ℝⁿ` containing the unit ball and of diameter at most `D`, the conductance of
hit-and-run on `K` is at least `lam/(245760·n·D)` when Lemma 4.1 holds with loss `lam`.

**Two hypotheses carry content, and they are not on the same footing.**

* `hIso` — **the open gap, in its corrected form.**  It is the paper's Theorem 2.1, the
  weighted isoperimetric inequality, specialised to the uniform density: for a partition
  `T₁, T₂, (K \ T₁) \ T₂` of `K` and a nonnegative weight `h` bounded by
  `(1/3)·min(1, d_K(u,v))` on every chord joining `T₁` to `T₂` **and by `1/3` on all of
  `K`**, the middle piece has mass at least `E_π(h)·min(π T₁, π T₂)`.

  The second bound is **not** in the paper, and Theorem 2.1 is false without it:
  `Arlib.not_hIso_two` refutes the uncorrected binder at `n = 2`, `K = [0,4]²`.  It is
  discharged at the use site below by `Arlib.MarkovChains.weight_le_third`, so it costs no
  caller anything; see §1 of the module docstring.

  What is still assumed is one invocation of the Localization Lemma (KLS 1995, Cor. 2.4) on
  a signed pair of integrands — **not** Borsuk–Ulam, which
  `Arlib.exists_flat_cut_zero_pos` shows is not needed.  Everything else in §2 of the paper
  is proved in `Arlib/Convexity/LovaszVempalaIso.lean` (`Arlib.needle_iso`,
  `Arlib.needle_iso_of_chord`, `Arlib.thm21_of_localization`).  `hIso` is written out inline
  here, as a `∀`-hypothesis, precisely so that it cannot be mistaken for something proved —
  and that is what made the paper's error findable.

* `hLem41` — **not a gap; work in flight.**  The paper's Lemma 4.1: two points close in
  cross-ratio distance *and* close relative to their median step lengths have one-step
  distributions at total variation distance less than `1 − 1/500`.  It is being proved in
  `Arlib/MarkovChains/Continuous/HitAndRunOverlap.lean`.  `Arlib.TVLe μ ν ε` is this
  repository's total-variation bound (`Arlib/Probability/TV.lean`), i.e. `d_TV(μ,ν) ≤ ε`;
  the paper's strict `<` is weakened to `≤`, which is all the proof consumes.

  It is demanded only on `interior K`, which is where the proof below applies it (`S₁'` and
  `S₂'` are cut down to the interior; see §1 of *Two places where the formalisation is more
  careful than the paper*).  That restriction is not cosmetic: the `∀ u ∈ K` form is
  **unreachable**, because the side condition `chordLow K u v < 0` of the proved Lemma 4.1
  is false at every boundary point (`Arlib.MarkovChains.chordLow_eq_zero_of_notMem_interior`).
  On the interior the binder is discharged outright, at `1 − 1/8000` for `n ≥ 1100`, by
  `Arlib.MarkovChains.hLem41_interior_uncond`; `conductance_hitAndRun_ge_of_tv` below is this
  theorem with the binder restored to `∀ u ∈ K` for backward compatibility.

**The paper's Lemma 3.3 is no longer among them.**  It used to appear here as a third inline
hypothesis `hLem33`, forwarded to `Arlib.lintegral_stepRadius_ge`.  That hypothesis is
**discharged**: Lemma 3.3 is proved in `Arlib/Convexity/KLS97Sharp.lean`
(`Arlib.lintegral_volume_closedBall_sdiff_le_sqrt`, specialised as `Arlib.lem33_sqrt`), and
`StepLength.lean` now consumes it internally from `hball`.  No `hLem33` binder remains.  The
price is its constant: the proved form is `10·t√n/2r`, which is why the conclusion below has
`245760` where the paper's arithmetic gives `24576`.

The remaining hypotheses are the standing geometric side conditions of the paper's own
statement: `K` convex, closed, measurable and bounded, containing a unit ball
`closedBall z 1` (at an arbitrary centre, as in the paper), of diameter at most `D`, and
`1 ≤ n`.  `hball` now does double duty: besides non-degeneracy — `0 < vol K` and
`1 ≤ diam K ≤ D` — it is what discharges Lemma 3.3 inside
`Arlib.lintegral_stepRadius_ge`, which is stated at inradius `r = 1`.  That is exactly the
paper's own "Suppose `K` contains a unit ball" for Lemma 3.4.

**Non-vacuity, stated honestly.**  No witness for the hypothesis bundle is exhibited here,
and none can be until `hIso` is proved.  This is not a formality: in the shape `hIso` had
before the `∀ x ∈ K, h x ≤ 1/3` clause was inserted, the bundle was **provably
unsatisfiable** at `n = 2`, `K = [0,4]²` (`Arlib.not_hIso_two`,
`Arlib.cexK_hitAndRun_hypotheses`), i.e. the theorem was vacuous there.  With the clause the
binder is the corrected Theorem 2.1, whose one-dimensional and needle forms are proved
(`Arlib.needle_iso`, `Arlib.needle_iso_of_chord`) and whose remaining content is a single
invocation of the Localization Lemma (`Arlib.thm21_of_localization`).  What *can* be said
otherwise is that no hypothesis is degenerate on its face — `hLem41` is discharged by the
paper's Lemma 4.1, and the geometric side conditions hold for, say, the unit ball itself. -/
theorem conductance_hitAndRun_ge_of_tv_interior (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hLem41 : ∀ u ∈ interior K, ∀ v ∈ interior K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - lam)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  haveI : NeZero n := ⟨hn'⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR0
  have hsqsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  obtain ⟨R, hR⟩ := hKb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hR)
  have hK0 : volume K ≠ 0 :=
    (lt_of_lt_of_le (measure_closedBall_pos volume z one_pos) (measure_mono hball)).ne'
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn hKb hball) hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hnD : (0 : ℝ) < (n : ℝ) * D := by positivity
  have hnD1 : (1 : ℝ) ≤ (n : ℝ) * D := by nlinarith
  haveI : IsProbabilityMeasure (uniformOn volume K) :=
    isProbabilityMeasure_uniformOn volume hK0 hKtop
  set pi : Measure (EuclideanSpace ℝ (Fin n)) := uniformOn volume K with hpidef
  set P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) := hitAndRun K with hPdef
  have hrev : IsReversible P pi := isReversible_hitAndRun hKm
  have hIm : MeasurableSet (interior K) := isOpen_interior.measurableSet
  -- the frontier is null, so `interior K` carries all the mass
  have hintc : pi (interior K)ᶜ = 0 := by
    have hsub : (interior K)ᶜ ⊆ Kᶜ ∪ frontier K := by
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inr (by rw [hKcl.frontier_eq]; exact ⟨hxK, hx⟩)
      · exact Or.inl hxK
    refine nonpos_iff_eq_zero.mp ?_
    calc pi (interior K)ᶜ ≤ pi (Kᶜ ∪ frontier K) := measure_mono hsub
      _ ≤ pi Kᶜ + pi (frontier K) := measure_union_le _ _
      _ = 0 := by
          rw [hpidef, uniformOn_compl_eq_zero volume hKm,
            uniformOn_absolutelyContinuous volume K (hKc.addHaar_frontier volume), add_zero]
  -- the walk leaves every interior point with probability one
  have hmove : ∀ x ∈ interior K, hitAndRunProposal K x Set.univ = 1 := by
    intro x hx
    obtain ⟨ε, hε, hbx⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    exact hitAndRunProposal_univ_eq_one_of_mem_interior hKm hε (hbx.trans interior_subset) hR
  -- the weight function `h(x) = s(x)/(48·D·√n)` of §4
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => stepRadius K (63 / 64) x / (48 * D * Real.sqrt n) with hgdef
  have hgapp : ∀ x, g x = stepRadius K (63 / 64) x / (48 * D * Real.sqrt n) := fun _ => rfl
  have hcpos : (0 : ℝ) < 48 * D * Real.sqrt n := by positivity
  have hgnn : ∀ x, 0 ≤ g x := fun x =>
    div_nonneg (stepRadius_nonneg hn' hKtop (by norm_num) x) hcpos.le
  -- Lemma 3.4 gives the average weight
  have hconst : 1 / (48 * D * Real.sqrt n) * ((1 - 63 / 64) / (10 * Real.sqrt n))
      = 1 / (30720 * (n : ℝ) * D) := by
    rw [show (1 : ℝ) - 63 / 64 = 1 / 64 by norm_num, div_mul_div_comm, one_mul, div_div]
    congr 1
    linear_combination (30720 * D) * hsqsq
  have hL34 : ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * volume K
      ≤ ∫⁻ x in K, ENNReal.ofReal (stepRadius K (63 / 64) x) :=
    lintegral_stepRadius_ge hn' hKc hKcl hKm hKtop (by norm_num) (by norm_num) hball
  have hpiint : (∫⁻ x, ENNReal.ofReal (g x) ∂pi)
      = ENNReal.ofReal (1 / (48 * D * Real.sqrt n)) *
          ((volume K)⁻¹ * ∫⁻ x in K, ENNReal.ofReal (stepRadius K (63 / 64) x)) := by
    have hrw : ∀ x, ENNReal.ofReal (g x)
        = ENNReal.ofReal (1 / (48 * D * Real.sqrt n))
            * ENNReal.ofReal (stepRadius K (63 / 64) x) := by
      intro x
      rw [hgapp x, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    simp only [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [hpidef, uniformOn_def, lintegral_smul_measure, smul_eq_mul]
  have hinv : ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n))
      ≤ (volume K)⁻¹ * ∫⁻ x in K, ENNReal.ofReal (stepRadius K (63 / 64) x) := by
    have hcancel : (volume K)⁻¹ * (ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * volume K)
        = ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) := by
      rw [show (volume K)⁻¹ * (ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * volume K)
            = ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * (volume K * (volume K)⁻¹) from
          by ring, ENNReal.mul_inv_cancel hK0 hKtop, mul_one]
    calc ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n))
        = (volume K)⁻¹ * (ENNReal.ofReal ((1 - 63 / 64) / (10 * Real.sqrt n)) * volume K) :=
          hcancel.symm
      _ ≤ _ := by gcongr
  have hint : ENNReal.ofReal (1 / (30720 * (n : ℝ) * D))
      ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂pi := by
    rw [hpiint, ← hconst, ENNReal.ofReal_mul (by positivity)]
    gcongr
  -- now the conductance
  refine le_conductance P pi fun S hSm hSpos hShalf => ?_
  have hpitop : pi S ≠ ⊤ := measure_ne_top _ _
  have hcompl : pi S + pi Sᶜ = 1 := by rw [measure_add_measure_compl hSm, measure_univ]
  have hSc : (1 : ℝ≥0∞) / 2 ≤ pi Sᶜ := by
    have h1 : (1 : ℝ≥0∞) / 2 + 1 / 2 ≤ 1 / 2 + pi Sᶜ := by
      calc (1 : ℝ≥0∞) / 2 + 1 / 2 = 1 := ENNReal.add_halves 1
        _ = pi S + pi Sᶜ := hcompl.symm
        _ ≤ 1 / 2 + pi Sᶜ := by gcongr
    exact (ENNReal.add_le_add_iff_left (by simp)).1 h1
  set eps : ℝ≥0∞ := ENNReal.ofReal (lam / 2) with hepsdef
  set S1 : Set (EuclideanSpace ℝ (Fin n)) :=
    (S ∩ interior K) ∩ {x | P x Sᶜ < eps} with hS1def
  set S2 : Set (EuclideanSpace ℝ (Fin n)) :=
    (interior K \ S) ∩ {x | P x S < eps} with hS2def
  have hS1m : MeasurableSet S1 :=
    (hSm.inter hIm).inter (measurableSet_lt (Kernel.measurable_coe P hSm.compl) measurable_const)
  have hS2m : MeasurableSet S2 :=
    (hIm.diff hSm).inter (measurableSet_lt (Kernel.measurable_coe P hSm) measurable_const)
  have hmem1 : ∀ x, x ∈ S1 ↔ ((x ∈ S ∧ x ∈ interior K) ∧ P x Sᶜ < eps) := by
    intro x; rw [hS1def]; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hmem2 : ∀ x, x ∈ S2 ↔ ((x ∈ interior K ∧ x ∉ S) ∧ P x S < eps) := by
    intro x; rw [hS2def]; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
  have hS1int : ∀ x ∈ S1, x ∈ interior K := fun x hx => ((hmem1 x).1 hx).1.2
  have hS2int : ∀ x ∈ S2, x ∈ interior K := fun x hx => ((hmem2 x).1 hx).1.1
  have hS1K : S1 ⊆ K := fun x hx => interior_subset (hS1int x hx)
  have hS2K : S2 ⊆ K := fun x hx => interior_subset (hS2int x hx)
  have hdisj : Disjoint S1 S2 :=
    Set.disjoint_left.mpr fun x hx1 hx2 => ((hmem2 x).1 hx2).1.2 ((hmem1 x).1 hx1).1.1
  -- the failure of Lemma 4.1 at a pair of deep points
  have hdich : ∀ u ∈ S1, ∀ v ∈ S2,
      1 / 8 ≤ crossRatioDist K u v ∨
        (medianStep K u ≤ Real.sqrt n / 2 * dist u v ∧
          medianStep K v ≤ Real.sqrt n / 2 * dist u v) := by
    intro u hu v hv
    rcases le_or_gt (1 / 8 : ℝ) (crossRatioDist K u v) with h8 | h8
    · exact Or.inl h8
    refine Or.inr ?_
    have hsep : ¬ dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) := by
      intro hlt
      have htv := hLem41 u (hS1int u hu) v (hS2int v hv) h8 hlt
      have hu' : P u Sᶜ < eps := ((hmem1 u).1 hu).2
      have hv' : P v S < eps := ((hmem2 v).1 hv).2
      have h1 : P u S ≤ P v S + ENNReal.ofReal (1 - lam) := (htv S hSm).1
      have hA : P u S < ENNReal.ofReal (lam / 2 + (1 - lam)) := by
        calc P u S ≤ P v S + ENNReal.ofReal (1 - lam) := h1
          _ < eps + ENNReal.ofReal (1 - lam) :=
              ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hv'
          _ = ENNReal.ofReal (lam / 2 + (1 - lam)) := by
              rw [hepsdef, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      have hsum : P u S + P u Sᶜ < 1 := by
        calc P u S + P u Sᶜ < ENNReal.ofReal (lam / 2 + (1 - lam)) + P u Sᶜ :=
              ENNReal.add_lt_add_right (measure_ne_top _ _) hA
          _ < ENNReal.ofReal (lam / 2 + (1 - lam)) + eps :=
              ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hu'
          _ = 1 := by
              rw [hepsdef, ← ENNReal.ofReal_add (by linarith) (by linarith),
                show lam / 2 + (1 - lam) + lam / 2 = 1 by ring, ENNReal.ofReal_one]
      rw [measure_add_measure_compl hSm, measure_univ] at hsum
      exact lt_irrefl _ hsum
    rw [not_lt] at hsep
    have hcpos2 : (0 : ℝ) < Real.sqrt n / 2 := by positivity
    have hid : Real.sqrt n / 2 * (2 / Real.sqrt n) = 1 := by field_simp
    have hmax : max (medianStep K u) (medianStep K v) ≤ Real.sqrt n / 2 * dist u v := by
      calc max (medianStep K u) (medianStep K v)
          = Real.sqrt n / 2 * (2 / Real.sqrt n * max (medianStep K u) (medianStep K v)) := by
            rw [← mul_assoc, hid, one_mul]
        _ ≤ Real.sqrt n / 2 * dist u v := mul_le_mul_of_nonneg_left hsep hcpos2.le
    exact ⟨le_trans (le_max_left _ _) hmax, le_trans (le_max_right _ _) hmax⟩
  -- Theorem 2.1's hypothesis, verified
  have hcond : ∀ u ∈ S1, ∀ v ∈ S2, ∀ x ∈ K,
      (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
      g x ≤ min 1 (crossRatioDist K u v) / 3 := by
    rintro u hu v hv x hxK ⟨t, hxt⟩
    have huv : u ≠ v := by
      intro h
      exact ((hmem2 v).1 hv).1.2 (h ▸ ((hmem1 u).1 hu).1.1)
    rw [hgapp x]
    exact weight_le_of_chord hn' hKc hKcl hKm hKb hKtop (by norm_num) (by norm_num) hD hD0
      (hS1int u hu) (hS2int v hv) huv (hmove u (hS1int u hu)) (hmove v (hS2int v hv))
      (hdich u hu v hv) hxK hxt
  -- the global bound `h ≤ 1/3` of Theorem 2.1, which the paper calls clear and which is
  -- *not* a consequence of the chord bound (`Arlib.not_hIso_two`)
  have hg13 : ∀ x ∈ K, g x ≤ 1 / 3 := by
    intro x hx
    rw [hgapp x]
    exact weight_le_third hn' hKb (by norm_num) hD hD0 hx
  have hisoS := hIso g S1 S2 hgnn hg13 hS1m hS2m hS1K hS2K hdisj hcond
  have hiso2 : ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) * min (pi S1) (pi S2)
      ≤ pi ((K \ S1) \ S2) := by
    refine le_trans ?_ hisoS
    gcongr
  -- the three-way partition and the flow accounting
  have hSA : S \ (S1 ∪ (interior K)ᶜ) = (S ∩ interior K) \ S1 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  have hSB : Sᶜ \ (S2 ∪ (interior K)ᶜ) = (interior K \ S) \ S2 := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hA' : ∀ x ∈ S \ (S1 ∪ (interior K)ᶜ), eps ≤ 1 * P x Sᶜ := by
    rw [hSA]
    rintro x ⟨⟨hxS, hxK⟩, hxS1⟩
    rw [one_mul]
    by_contra hc
    exact hxS1 ((hmem1 x).2 ⟨⟨hxS, hxK⟩, not_le.1 hc⟩)
  have hB' : ∀ x ∈ Sᶜ \ (S2 ∪ (interior K)ᶜ), eps ≤ 1 * P x S := by
    rw [hSB]
    rintro x ⟨⟨hxK, hxS⟩, hxS2⟩
    rw [one_mul]
    by_contra hc
    exact hxS2 ((hmem2 x).2 ⟨⟨hxK, hxS⟩, not_le.1 hc⟩)
  have hflow : eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))
      ≤ 2 * (1 * flow P pi S Sᶜ) := by
    have h := mul_measure_add_measure_le_mul_flow P pi hrev hSm (hS1m.union hIm.compl)
      (hS2m.union hIm.compl) hA' hB'
    rwa [hSA, hSB] at h
  have hflow' : eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))
      ≤ 2 * flow P pi S Sᶜ := by rwa [one_mul] at hflow
  have hpart : pi ((K \ S1) \ S2)
      ≤ pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2) := by
    have hsub : (K \ S1) \ S2 ⊆ (((S ∩ interior K) \ S1) ∪ ((interior K \ S) \ S2))
        ∪ (interior K)ᶜ := by
      rintro x ⟨⟨hxK, hxS1⟩, hxS2⟩
      by_cases hxI : x ∈ interior K
      · by_cases hxS : x ∈ S
        · exact Or.inl (Or.inl ⟨⟨hxS, hxI⟩, hxS1⟩)
        · exact Or.inl (Or.inr ⟨⟨hxI, hxS⟩, hxS2⟩)
      · exact Or.inr hxI
    calc pi ((K \ S1) \ S2)
        ≤ pi ((((S ∩ interior K) \ S1) ∪ ((interior K \ S) \ S2)) ∪ (interior K)ᶜ) :=
          measure_mono hsub
      _ ≤ pi (((S ∩ interior K) \ S1) ∪ ((interior K \ S) \ S2)) + pi (interior K)ᶜ :=
          measure_union_le _ _
      _ ≤ pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2) + pi (interior K)ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2) := by rw [hintc, add_zero]
  have hcov1 : pi S ≤ pi ((S ∩ interior K) \ S1) + pi S1 := by
    have hsub : S ⊆ (((S ∩ interior K) \ S1) ∪ S1) ∪ (interior K)ᶜ := by
      intro x hx
      by_cases hxI : x ∈ interior K
      · by_cases hxS1 : x ∈ S1
        · exact Or.inl (Or.inr hxS1)
        · exact Or.inl (Or.inl ⟨⟨hx, hxI⟩, hxS1⟩)
      · exact Or.inr hxI
    calc pi S ≤ pi ((((S ∩ interior K) \ S1) ∪ S1) ∪ (interior K)ᶜ) := measure_mono hsub
      _ ≤ pi (((S ∩ interior K) \ S1) ∪ S1) + pi (interior K)ᶜ := measure_union_le _ _
      _ ≤ pi ((S ∩ interior K) \ S1) + pi S1 + pi (interior K)ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((S ∩ interior K) \ S1) + pi S1 := by rw [hintc, add_zero]
  have hcov2 : pi Sᶜ ≤ pi ((interior K \ S) \ S2) + pi S2 := by
    have hsub : Sᶜ ⊆ (((interior K \ S) \ S2) ∪ S2) ∪ (interior K)ᶜ := by
      intro x hx
      by_cases hxI : x ∈ interior K
      · by_cases hxS2 : x ∈ S2
        · exact Or.inl (Or.inr hxS2)
        · exact Or.inl (Or.inl ⟨⟨hxI, hx⟩, hxS2⟩)
      · exact Or.inr hxI
    calc pi Sᶜ ≤ pi ((((interior K \ S) \ S2) ∪ S2) ∪ (interior K)ᶜ) := measure_mono hsub
      _ ≤ pi (((interior K \ S) \ S2) ∪ S2) + pi (interior K)ᶜ := measure_union_le _ _
      _ ≤ pi ((interior K \ S) \ S2) + pi S2 + pi (interior K)ᶜ := by
          gcongr
          exact measure_union_le _ _
      _ = pi ((interior K \ S) \ S2) + pi S2 := by rw [hintc, add_zero]
  -- the arithmetic of the final constant
  have h4c : (4 : ℝ≥0∞) * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))
      = ENNReal.ofReal (4 * (lam / (245760 * (n : ℝ) * D))) := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  have hcmp1 : (4 : ℝ≥0∞) * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) ≤ eps := by
    rw [h4c, hepsdef]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show 4 * (lam / (245760 * (n : ℝ) * D)) = lam / (61440 * ((n : ℝ) * D)) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hcmp3 : (4 : ℝ≥0∞) * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))
      ≤ eps * ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) := by
    rw [h4c, hepsdef, ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    field_simp
    ring
  -- the three branches
  have hmain : 4 * (ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) * pi S)
      ≤ 4 * flow P pi S Sᶜ := by
    by_cases hc1 : pi S ≤ 2 * pi ((S ∩ interior K) \ S1)
    · calc 4 * (ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) * pi S)
          = (4 * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))) * pi S := by ring
        _ ≤ eps * pi S := by gcongr
        _ ≤ eps * (2 * pi ((S ∩ interior K) \ S1)) := by gcongr
        _ = 2 * (eps * pi ((S ∩ interior K) \ S1)) := by ring
        _ ≤ 2 * (eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))) := by
            gcongr
            exact le_self_add
        _ ≤ 2 * (2 * flow P pi S Sᶜ) := by gcongr
        _ = 4 * flow P pi S Sᶜ := by ring
    by_cases hc2 : pi Sᶜ ≤ 2 * pi ((interior K \ S) \ S2)
    · calc 4 * (ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) * pi S)
          = (4 * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))) * pi S := by ring
        _ ≤ eps * pi S := by gcongr
        _ ≤ eps * pi Sᶜ := mul_le_mul_right (hShalf.trans hSc) eps
        _ ≤ eps * (2 * pi ((interior K \ S) \ S2)) := by gcongr
        _ = 2 * (eps * pi ((interior K \ S) \ S2)) := by ring
        _ ≤ 2 * (eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))) := by
            gcongr
            exact le_add_self
        _ ≤ 2 * (2 * flow P pi S Sᶜ) := by gcongr
        _ = 4 * flow P pi S Sᶜ := by ring
    rw [not_le] at hc1 hc2
    have h1 : pi S < 2 * pi S1 := by
      have hstep : pi S + pi S < pi S + 2 * pi S1 := by
        calc pi S + pi S = 2 * pi S := (two_mul _).symm
          _ ≤ 2 * (pi ((S ∩ interior K) \ S1) + pi S1) := by gcongr
          _ = 2 * pi ((S ∩ interior K) \ S1) + 2 * pi S1 := by ring
          _ < pi S + 2 * pi S1 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc1
      exact (ENNReal.add_lt_add_iff_left hpitop).1 hstep
    have h2 : pi Sᶜ < 2 * pi S2 := by
      have hstep : pi Sᶜ + pi Sᶜ < pi Sᶜ + 2 * pi S2 := by
        calc pi Sᶜ + pi Sᶜ = 2 * pi Sᶜ := (two_mul _).symm
          _ ≤ 2 * (pi ((interior K \ S) \ S2) + pi S2) := by gcongr
          _ = 2 * pi ((interior K \ S) \ S2) + 2 * pi S2 := by ring
          _ < pi Sᶜ + 2 * pi S2 :=
              ENNReal.add_lt_add_right
                (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _)) hc2
      exact (ENNReal.add_lt_add_iff_left (measure_ne_top _ _)).1 hstep
    have h2' : pi S < 2 * pi S2 := lt_of_le_of_lt (hShalf.trans hSc) h2
    have hmin : pi S ≤ 2 * min (pi S1) (pi S2) := by
      rcases le_total (pi S1) (pi S2) with h | h
      · rw [min_eq_left h]; exact h1.le
      · rw [min_eq_right h]; exact h2'.le
    calc 4 * (ENNReal.ofReal (lam / (245760 * (n : ℝ) * D)) * pi S)
        = (4 * ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))) * pi S := by ring
      _ ≤ (eps * ENNReal.ofReal (1 / (30720 * (n : ℝ) * D))) * pi S := by gcongr
      _ = eps * (ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) * pi S) := by ring
      _ ≤ eps * (ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) * (2 * min (pi S1) (pi S2))) := by
          gcongr
      _ = 2 * (eps * (ENNReal.ofReal (1 / (30720 * (n : ℝ) * D)) * min (pi S1) (pi S2))) := by
          ring
      _ ≤ 2 * (eps * pi ((K \ S1) \ S2)) := by gcongr
      _ ≤ 2 * (eps * (pi ((S ∩ interior K) \ S1) + pi ((interior K \ S) \ S2))) := by gcongr
      _ ≤ 2 * (2 * flow P pi S Sᶜ) := by gcongr
      _ = 4 * flow P pi S Sᶜ := by ring
  rw [conductanceOn_apply, ENNReal.le_div_iff_mul_le (Or.inl hSpos.ne') (Or.inl hpitop)]
  have h4ne : (4 : ℝ≥0∞) ≠ 0 := by norm_num
  have h4top : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  exact (ENNReal.mul_le_mul_iff_right h4ne h4top).mp hmain

/-- **Theorem 4.2 with `hLem41` demanded on all of `K`** — the shape this theorem had before
`conductance_hitAndRun_ge_of_tv_interior` was split off, kept verbatim so that every existing
consumer continues to typecheck.

The proof is the whole content of the claim that the split is a *strengthening*: a caller
holding Lemma 4.1 on all of `K` gets it on `interior K` by `interior_subset`, so nothing that
could be proved from this statement is lost by the weaker binder.  The converse fails, and
that is the point: **the `∀ u ∈ K` form is not obtainable from the paper's Lemma 4.1.**
`Arlib.MarkovChains.tvLe_hitAndRun_lemma41_uncond` (`SphereCap.lean`) needs
`chordLow K u v < 0`, and for `u ∈ frontier K` and `v ∈ interior K` that is *false*: a point
`u + t(v−u) ∈ K` with `t < 0` would put `u` on an open segment between a point of `K` and an
interior point, hence in `interior K`.  So `chordLow K u v = 0` there, for every body, in
every dimension.  On `interior K` the same side condition is
`Arlib.chordLow_neg_of_mem_interior`, and the discharged binder is
`Arlib.MarkovChains.hLem41_interior_uncond` (`HitAndRunLem41Discharge.lean`). -/
theorem conductance_hitAndRun_ge_of_tv (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - lam)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (lam / (245760 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_tv_interior hn hKc hKcl hKm hKb hball hD hlam0 hlam1
    (fun u hu v hv => hLem41 u (interior_subset hu) v (interior_subset hv)) hIso

/-- **Theorem 4.2 of Lovász–Vempala, at the paper's Lemma 4.1 constant.**

    Φ(hit-and-run on K)  ≥  1/(2²⁷·n·D).

This is `Arlib.MarkovChains.conductance_hitAndRun_ge_of_tv_interior` at the paper's Lemma 4.1 loss
`lam = 1/500`, where the general bound reads `1/(500·245760·n·D) = 1/(122880000·n·D)`.

**Why `2²⁷` and not the paper's `2²⁴`.**  The exact constant the proof delivers is
`122880000`, and `122880000 > 2²⁴ = 16777216`, so the paper's power of two is *not* what this
route proves and is not claimed.  The statement is rounded up to the next power of two,
`2²⁷ = 134217728 ≥ 122880000`, purely for legibility — the exact form
`1/(122880000·n·D)` is available by rerunning the final comparison, and is strictly stronger.

The whole gap to the paper is one factor `10`: the proved Lemma 3.3
(`Arlib.lem33_sqrt`) reads `10·t√n/2r` where the paper writes `t√n/2r`, so Lemma 3.4 reads
`∫_K s ≥ ((1−α)/(10√n))·vol K`, and `10 · 12288000 = 122880000`.  That `10` is a
constant-factor loss in the exponential-envelope majorant used by `KLS97Sharp.lean` — **not**
an error in KLS 1997, and not a change in the order of the bound, which remains the paper's
`1/(n·D)` up to an absolute constant.

Read the docstring of `conductance_hitAndRun_ge_of_tv_interior` for the classification of the
hypotheses: `hIso` is the **open gap, in its corrected form** (the paper's Theorem 2.1, which
is *false* as printed — `Arlib.not_hIso_two` — and which needs the Localization Lemma on
signed integrands, but **not** Borsuk–Ulam); `hLem41` is a placeholder for
work in flight elsewhere in this repository; and the paper's Lemma 3.3 is **proved**, in
`Arlib/Convexity/KLS97Sharp.lean`, and is no longer a hypothesis of either theorem. -/
theorem conductance_hitAndRun_ge_interior (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ interior K, ∀ v ∈ interior K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hD1 : (1 : ℝ) ≤ D := le_trans (one_le_diam_of_unitBall hn hKb hball) hD
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (conductance_hitAndRun_ge_of_tv_interior hn hKc hKcl hKm hKb hball hD (by norm_num)
      (by norm_num) hLem41 hIso)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Theorem 4.2 at `1/(2²⁷·n·D)` with `hLem41` demanded on all of `K`** — the shape this
theorem had before `conductance_hitAndRun_ge_interior` was split off, kept verbatim so that
every existing consumer continues to typecheck, and derived from the interior form by
`interior_subset`.  See `conductance_hitAndRun_ge_of_tv`'s docstring for why the `∀ u ∈ K`
form is the one that cannot be discharged. -/
theorem conductance_hitAndRun_ge (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500)))
    (hIso : ∀ (h : EuclideanSpace ℝ (Fin n) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin n))), (∀ x, 0 ≤ h x) →
      (∀ x ∈ K, h x ≤ 1 / 3) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ K → T₂ ⊆ K → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ K,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin n)) t) →
        h x ≤ min 1 (crossRatioDist K u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume K)) *
          min (uniformOn volume K T₁) (uniformOn volume K T₂)
        ≤ uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_interior hn hKc hKcl hKm hKb hball hD
    (fun u hu v hv => hLem41 u (interior_subset hu) v (interior_subset hv)) hIso

/-! ## Axiom profile -/

section AxiomCheck

#print axioms stepRadius_le_two_mul_diam
#print axioms weight_le_third
#print axioms stepRadius_le_of_chord
#print axioms weight_le_of_chord
#print axioms one_le_diam_of_unitBall
#print axioms conductance_hitAndRun_ge_of_tv_interior
#print axioms conductance_hitAndRun_ge_of_tv
#print axioms conductance_hitAndRun_ge_interior
#print axioms conductance_hitAndRun_ge

end AxiomCheck

end Arlib.MarkovChains
