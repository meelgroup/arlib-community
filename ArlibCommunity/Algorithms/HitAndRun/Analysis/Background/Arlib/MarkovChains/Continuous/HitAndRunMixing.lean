/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunConductance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.MixingFromConductance

/-!
# Theorem 1.1 of Lovász–Vempala: mixing of hit-and-run from an almost-warm start

> L. Lovász and S. Vempala, *Hit-and-Run from a Corner*, STOC 2004 / SIAM J. Comput. 35
> (2006) 985–1005, §1 and §5.

> **Theorem 1.1.** Let `K` be a convex body containing a ball of radius `r` and contained
> in a ball of radius `R`.  Let `σ` be a starting distribution and `σ_m` the law after `m`
> steps of hit-and-run in `K`.  Let `ε > 0` and suppose `dσ/dπ_K ≤ M` except on a set `S`
> with `σ(S) ≤ ε/2`.  Then for `m > 10¹⁰·n²·(R²/r²)·ln(M/ε)`, `d_TV(σ_m, π_K) < ε`.

This file proves the **structural** content of that theorem — the exceptional-set split and
the conversion of a conductance bound into a step count — and is explicit about the two
things it does not prove.  Read §"What is assumed" before using anything here.

## The paper's actual proof (and a correction to a widespread misreading)

§5 of *Hit-and-Run from a Corner* is one page and does **not** use `s`-conductance.  It uses
the *ordinary* conductance `Φ` of §1.1 together with Corollary 1.5 of Lovász–Simonovits
(RSA 1993), quoted there as

    d_TV(μ_m, π)  ≤  √M · (1 − Φ²/2)^m       for an `M`-warm start `μ`.

The logarithmic dependence on `M` and `ε` in Theorem 1.1 comes from the `√M` in *that*
bound — `√M (1−Φ²/2)^m ≤ ε` needs only `m ≳ Φ⁻² ln(M/ε²)` — and **not** from an
`s`-conductance argument.  (`s`-conductance is what Lovász–Simonovits need for the *ball
walk*, whose small sets have arbitrarily bad conductance; the whole point of §4 of
Lovász–Vempala is that hit-and-run needs no such device, because its conductance bound
holds for *every* subset.  The paper says so in §1: "a bound of `Ω(r/nR)` on the conductance
of every subset (Theorem 4.2) (for the ball walk, the conductance of small sets can be
arbitrarily small; therefore the need for a warm start)".)

For the record, and because it costs thirty lines, the `s`-conductance `Φ_s` is defined
below and the comparison `Φ ≤ Φ_s` — the formal content of "no loss" — is proved
(`conductance_le_conductanceS`).  Nothing else in this file uses it.

## What is proved here, unconditionally

*The exceptional-set split* (`§ Exceptional starts`).  This is the crux glue of §5, and it
is proved with no hypotheses beyond measurability:

* `Arlib.MarkovChains.restrictOff σ S = (σ Sᶜ)⁻¹ • σ.restrict Sᶜ` — the start conditioned
  on avoiding the exceptional set.
* `Arlib.MarkovChains.isProbabilityMeasure_restrictOff` — it is a probability measure.
* `Arlib.MarkovChains.tvLe_restrictOff` — `d_TV(σ, σ|Sᶜ) ≤ σ(S)`.  Note the constant: the
  naive estimate gives `2σ(S)`, and the sharp `σ(S)` is what makes the paper's `ε/2 + ε/2`
  bookkeeping close exactly.
* `Arlib.MarkovChains.isWarm_restrictOff` — if `σ(A ∖ S) ≤ M·π(A)` for every `A` and
  `σ(S) ≤ 1/2`, then `σ|Sᶜ` is `2M`-warm.  This is the paper's "we think of a random point
  of `K` as being generated with probability `1 − ε/2` from a distribution `μ₀` that is
  `(2M)`-warm".
* `Arlib.MarkovChains.tvLe_iterate_of_exceptional` — the assembled split: the chain started
  from `σ` is within `σ(S) + b` of `π` whenever the chain started from `σ|Sᶜ` is within `b`.
  Uses the kernel data-processing inequality `tvLe_iterate` of `Warmness.lean`.

*The step-count arithmetic* (`§ From a decay rate to a deadline`).

* `Arlib.MarkovChains.log_sqrt_two_mul_div` — `log(√(2M)/(ε/2)) = log(8M/ε²)/2`.
* `Arlib.MarkovChains.lsThreshold M phi eps = log(8M/eps²)/phi²` and
  `Arlib.MarkovChains.sqrt_mul_pow_le_of_lsThreshold_le`:
  `√(2M)·(1 − φ²/2)^m ≤ ε/2` once `m ≥ lsThreshold M φ ε`.

*The assembly* (`§ Theorem 1.1, for an arbitrary Markov chain`).

* `Arlib.MarkovChains.tvLe_iterate_of_exceptional_of_ls` — Theorem 1.1 for an arbitrary
  Markov kernel, given the Lovász–Simonovits decay bound as an explicit binder.

*The `s`-conductance route* (`§ The s-conductance route to the same deadline`).  A second,
independent derivation of the logarithmic dependence, which is what a chain whose small sets
misbehave (the ball walk) is forced to use:

* `Arlib.MarkovChains.conductanceSOn`, `MidSets`, `conductanceS` — the definition of `Φ_s`.
* `Arlib.MarkovChains.conductance_le_conductanceS` — **`Φ ≤ Φ_s`**: a conductance bound valid
  for *every* subset, which is what Theorem 4.2 supplies, is an `Φ_s` bound with no loss at
  any `s`.  `le_conductanceS` is the same fact in the form a caller uses.
* `Arlib.MarkovChains.SmallSetDiscrepancy` and `smallSetDiscrepancy_of_isWarm` — the
  Lovász–Simonovits `H_s`, and `H_s ≤ M·s` for an `M`-warm start.  *This* is why the
  `s`-conductance route also gives `log(M/ε)`: choosing `s = ε/(2M)` makes the additive term
  `ε/2` at a cost of only `log M` in the exponent.
* `Arlib.MarkovChains.lsThresholdS M phi eps = 2·log(2M/ε)/phi²` and
  `mul_pow_le_of_lsThresholdS_le`.
* `Arlib.MarkovChains.tvLe_iterate_of_sConductance` — **mixing from `s`-conductance**: an
  `M`-warm start reaches total variation `ε` after `2 log(2M/ε)/Φ_s²` steps, given the
  Lovász–Simonovits `s`-conductance bound `H_s + (H_s/s)(1 − Φ_s²/2)^m` as a binder.

*The hit-and-run instance* (`§ Theorem 1.1 for hit-and-run`).

* `Arlib.MarkovChains.lvThreshold n r R M eps = 2⁵⁶·n²·(R²/r²)·log(8M/ε²)`, identified with
  `lsThreshold` at `phi = r/(2²⁸ n R)` by `lsThreshold_eq_lvThreshold`.
* `Arlib.MarkovChains.tvLe_iterate_hitAndRun` — the statement of Theorem 1.1, at that
  threshold, for `Arlib.MarkovChains.hitAndRun K` and `Arlib.uniformOn volume K`.
* `Arlib.MarkovChains.ofReal_inv_le_conductance_hitAndRun_of_unitBall` — the `r = 1` case of
  the conductance hypothesis, discharged from `conductance_hitAndRun_ge` (Theorem 4.2) via
  `D ≤ 2R`.
* `Arlib.MarkovChains.tvLe_iterate_hitAndRun_unitBall` — the two combined: Theorem 1.1 for a
  body with a unit inball, with `hphi` discharged, leaving only `hLem41`, `hIso` and `hLS`.

  **`hIso` carries a clause that is not in Lovász–Vempala's Theorem 2.1**, namely
  `∀ x ∈ K, h x ≤ 1/3`.  Theorem 2.1 is *false* without it — `Arlib.not_hIso_two`
  (`Arlib/Convexity/LovaszVempalaIsoFalse.lean`) refutes the printed statement at `n = 2`,
  `K = [0,4]²` — so before the clause was inserted both theorems here were **vacuous** at
  that instance.  The clause costs nothing: it is the paper's own "clearly `h(x) ≤ 1/3`",
  proved as `Arlib.MarkovChains.weight_le_third`, and it is discharged inside
  `conductance_hitAndRun_ge_of_tv`, not by any caller.

*Non-vacuity* (`CLAUDE.md` §11).

* `Arlib.MarkovChains.ls_const` — the instantly mixing kernel satisfies the `hLS` binder.
* `Arlib.MarkovChains.tvLe_iterate_const_piHalf` — every hypothesis of
  `tvLe_iterate_of_exceptional_of_ls` is satisfiable *at once*, with a non-trivial
  conclusion, and the conclusion is derived through that theorem.

## What is assumed

Three things, all written **inline as `∀`-binders of the theorems that consume them**.
There is no `def`, `structure` field or `class` in this file whose name stands in for a
statement it does not prove.  Each has a machine-checked satisfiability witness.

**(A) `hLS` — Corollary 1.5 of Lovász–Simonovits (1993).**

    ∀ phi W, 0 < phi → phi ≤ 1 → 1 ≤ W → ofReal phi ≤ conductance P pi →
      ∀ mu, IsProbabilityMeasure mu → IsWarm (ofReal W) mu pi →
        ∀ t, TVLe (iterate P mu t) pi (ofReal (√W · (1 − phi²/2)^t))

⚠ **This paragraph used to claim the implication is "not proved anywhere in this
repository".  That was FALSE, and is corrected here (2026-08-11).**  The Cheeger inequality
and the spectral-gap⟹TV passage are *both* proved, and had been since 2026-08-08/09:
`Arlib.MarkovChains.sq_conductance_div_two_le_spectralGap` (`Cheeger.lean`, the hard
direction) and `Arlib.MarkovChains.tvLe_iterate_of_ofReal_le_conductance` (`L2Mixing.lean`,
whose conclusion is literally the body of the `hLS` binder below), both axiom-clean.
`MixingFromConductance.lean`'s corresponding passage is stale in the same way: it is true of
*that file*, but `Cheeger.lean` and `L2Mixing.lean` import it and supply exactly the pieces
it lists as missing.

`Arlib/MarkovChains/Continuous/ConductanceToTV.lean` therefore **discharges `hLS`**:
`Arlib.MarkovChains.ls_of_hasNonnegSpectrum` proves this binder verbatim from
`IsReversible`, `HasNonnegSpectrum` and a nonempty `SmallSets`, and `ls_lazy` proves it for
`lazy P` from reversibility alone.  What is *not* reachable is `hLS` for the **plain**
`hitAndRun K` kernel, which needs a hit-and-run-specific spectral fact — and that is exactly
the paper's own gap recorded as error 2 below, not a formalisation shortfall.

**It is false for a general reversible Markov kernel, and this file is the first place that
is recorded.**  Take `Ω = Bool`, `P x = dirac (!x)` (the swap kernel), `pi = piHalf`.  `P` is
reversible with respect to `piHalf` and its conductance is exactly `1`.  Started from
`dirac true` — which is `2`-warm — the iterate alternates between `dirac true` and
`dirac false`, so `d_TV(iterate P (dirac true) t, piHalf) = 1/2` for **every** `t`, while
`√2·(1 − 1²/2)^t = √2·2^{-t} → 0`.  So the binder needs a spectral hypothesis (laziness, or
a nonnegative spectrum) that Lovász–Vempala's §5 does not state when it applies the
corollary to the *non-lazy* hit-and-run kernel.  See `§ Errors in the paper` below.  The
binder is nonetheless satisfiable: `Arlib.MarkovChains.ls_const` discharges it for the
instantly-mixing kernel, which is the non-vacuity witness of `CLAUDE.md` §11.

**(A') `hLSs` — Corollary 1.5 of Lovász–Simonovits, `s`-conductance form.**  Used only by
`tvLe_iterate_of_sConductance`.  It is **false on a measurable space with atoms** — a
two-line counterexample on `Bool` is written out in
`§ A non-vacuity witness for the hLSs binder`, and it is a scope caveat on [11] rather than
on Lovász–Vempala.  It is satisfiable (`lsS_deterministic_id`), and the hit-and-run
application is atomless, so the caveat does not bite there.

**(B) `hphi` — Theorem 4.2 in the `r`/`R` form.**

    ofReal (r / (2^28 * n * R)) ≤ conductance (hitAndRun K) (uniformOn volume K)

`Arlib.MarkovChains.conductance_hitAndRun_ge` (in `HitAndRunConductance.lean`, itself
conditional on the paper's Theorem 2.1) proves `Φ ≥ 1/(2²⁷·n·D)` for a body of diameter `D`
containing a **unit** ball.  `ofReal_inv_le_conductance_hitAndRun_of_unitBall` below
discharges `hphi` from it in the case `r = 1`, using `D ≤ 2R`.  The general `r` is the
paper's "hit-and-run is invariant under a scaling of space (i.e. there is a 1–1 mapping
between the random walk in `K` and `cK`)"; ~~the equivariance
`(hitAndRun (c • K)).map (c • ·) = ...` is **not** proved in this repository~~ — **STALE,
corrected 2026-08-12.** It **is** proved: `Ttc.map_hitAndRun_chart`
(`Ttc/Sampler/HitAndRunBackend.lean`) gives
`Measure.map (r • · + zin) (hitAndRun ((r • · + zin) ⁻¹' K) y) = hitAndRun K (r • y + zin)`
for **every** `y`, with no membership hypothesis. Note the equivariance is under
*similarities* only, not general affine maps: hit-and-run's direction law is `unifSphere n`,
which is Euclidean-metric-dependent; a uniform scaling plus a translation is a similarity,
so the `r`/`zin` chart is covered and a general linear chart is not. `hphi` is still threaded
as a hypothesis in *this* file, which is untouched by the above.

## The constant, honestly (`CLAUDE.md` §11)

`lvThreshold` is `2⁵⁶·n²·(R²/r²)·ln(8M/ε²)`.  In the paper's shape — using
`ln(8M/ε²) ≤ ln 8 + 2 ln(M/ε)` for `M ≥ 1`, `0 < ε ≤ 1` — that is at most

    2⁵⁷ · n² · (R²/r²) · ln(M/ε)  +  2⁵⁶ ln 8 · n² · (R²/r²)
      ≈  1.4 × 10¹⁷ · n² (R²/r²) ln(M/ε) + …

against the paper's `10¹⁰ · n² (R²/r²) ln(M/ε)`.  The gap is a factor of about `10⁷`, and
**most of it is the paper's own**, not this repository's: see `§ Errors in the paper`.

## Errors and gaps found in the paper (`CLAUDE.md` §5)

1. **`10¹⁰` in Theorem 1.1 does not follow from `2²⁴` in Theorem 4.2.**  *Genuine numerical
   error.*  Theorem 4.2 gives `Φ ≥ 1/(2²⁴ n D)` for inradius `1`; scaling by `r` and using
   `D ≤ 2R` gives `Φ ≥ r/(2²⁵ n R)`.  Corollary 1.5 then needs
   `m ≳ 2/Φ² · ln(√M/ε) = 2⁵¹ · n²(R²/r²) · ln(√M/ε)`, and `2⁵¹ ≈ 2.25 × 10¹⁵`.  The
   paper's `10¹⁰` is smaller by a factor `≈ 2 × 10⁵`.  Equivalently: `10¹⁰` requires
   `Φ ≥ 1.4 × 10⁻⁵ · r/(nR)`, i.e. a constant near `2¹⁶`, where the paper's own Theorem 4.2
   delivers `2²⁵`.  §5 never performs this arithmetic — it writes only "`m > C n²R²/r²
   ln(M/ε)` steps (`C` is a constant)" — so the discrepancy is invisible in the text.  *The
   theorem is true with a larger absolute constant; only the printed `10¹⁰` is wrong.*
2. **Corollary 1.5 is applied to a chain with no laziness or spectral hypothesis.**
   *Genuine gap.*  The bound `√M(1−Φ²/2)^m` fails for reversible chains with negative
   spectrum; the swap kernel on `Bool` above is a two-line counterexample.  Lovász–Vempala
   apply it to hit-and-run, which is *not* made lazy anywhere in the paper.  Hit-and-run
   does hold at its current point with positive probability whenever the chord is short,
   which is morally the missing laziness, but the paper never says this and §5 quotes
   Corollary 1.5 unmodified.
3. **`√(2M/ε)` where `√(2M)` is what the argument gives.**  *Fine, implicit — an
   overestimate.*  §5's displayed bound is
   `d_TV(μ_m,π) ≤ ε/2 + (1−ε/2)√(2M/ε)(1−Φ²/2)^m`, but the `μ₀` it constructs is
   `(2M)`-warm, so Corollary 1.5 gives the strictly better `√(2M)`.  The displayed form is
   still *true* for `ε ≤ 1` (it is larger), so nothing downstream breaks; the `1/ε` appears
   to be a leftover from the `L₂` paragraph that follows, where `2M/ε` genuinely replaces
   `M`.  This file proves the sharp `√(2M)` form.
4. **Corollary 1.5 of [11] in `s`-conductance form is false on spaces with atoms.**
   *Genuine scope error, in the reference rather than in Lovász–Vempala.*  The bound
   `d_TV(σ_m,π) ≤ H_s + (H_s/s)(1 − Φ_s²/2)^m` is usually quoted with no hypothesis on the
   state space, but its proof needs `π` atomless: with atoms `H_s` can be `0` while
   `d_TV(σ_0,π) = 1/2`.  Counterexample and discussion in
   `§ A non-vacuity witness for the hLSs binder`.  Harmless for hit-and-run, whose target
   `uniformOn volume K` on `ℝⁿ` is atomless.
5. **The `ε/2 + …` split needs `σ(S) ≤ 1/2`, which is not stated.**  *Boundary
   imprecision.*  "we think of a random point of `K` as being generated with probability
   `1 − ε/2` from a distribution `μ₀` that is `(2M)`-warm" is only correct because
   `1 − ε/2 ≥ 1/2`, which uses `ε ≤ 1`.  Theorem 1.1 says only "`ε > 0`".  At `ε > 1` the
   conclusion `d_TV < ε` is vacuous anyway, so this is harmless, but the `2` in `(2M)`-warm
   is `1/(1 − ε/2)` and is unexplained in the text.  Formalised here as the explicit
   hypothesis `heps1 : eps ≤ 1`, which the sampler contract in
   `Ttc/Sampler/HitAndRunTheorem11.lean` also carries.

## Reused rather than rebuilt

* `Arlib.TVLe` and its pseudometric laws (`Arlib/Probability/TV.lean`).
* `Arlib.MarkovChains.iterate`, `tvLe_iterate` (the kernel data-processing inequality),
  `IsWarm`, `isWarm_iterate` (`Warmness.lean`).  The brief's claim that the data-processing
  inequality is missing refers to `TV.lean`; `Warmness.lean` has had it since
  `lintegral_le_of_tvLe`.
* `Arlib.MarkovChains.mixingTime`, `mul_pow_le_of_mixingTime_le`
  (`MixingFromConductance.lean`).
* `Arlib.MarkovChains.conductance`, `conductanceOn`, `flow` (`Conductance.lean`).
* `Arlib.MarkovChains.conductance_hitAndRun_ge` (`HitAndRunConductance.lean`).
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## `s`-conductance

Recorded for completeness; **nothing else in this file uses it**, because §5 of
*Hit-and-Run from a Corner* does not (see the module docstring).  The one substantive
statement is `conductance_le_conductanceS`: a conductance bound valid for *every* set — which
is what Theorem 4.2 provides — is a bound on `Φ_s` with no loss whatsoever. -/

/-- The **`s`-conductance of a single set**, `flow(S, Sᶜ) / (π(S) − s)`.  This is the
Lovász–Simonovits variant in which the small sets are discounted: the denominator is the
mass of `S` *in excess of* `s`, so a set of mass close to `s` is required to leak almost
nothing.  As always in `ℝ≥0∞`, division by `0` is `0`, so the definition has content only
when `s < π(S)`. -/
noncomputable def conductanceSOn (P : Kernel Ω Ω) (pi : Measure Ω) (s : ℝ≥0∞) (S : Set Ω) :
    ℝ≥0∞ :=
  flow P pi S Sᶜ / (pi S - s)

/-- The sets the `s`-conductance infimum ranges over: measurable sets whose mass lies
strictly above `s` and at most `1/2`. -/
def MidSets (pi : Measure Ω) (s : ℝ≥0∞) : Set (Set Ω) :=
  {S : Set Ω | MeasurableSet S ∧ s < pi S ∧ pi S ≤ 1 / 2}

/-- The **`s`-conductance** `Φ_s = inf { flow(S,Sᶜ)/(π(S) − s) : s < π(S) ≤ 1/2 }`.

Lovász–Simonovits write the infimum over `s < π(S) < 1 − s` with denominator
`min(π(S), π(Sᶜ)) − s`.  For a **reversible** chain the two agree: `flow(S,Sᶜ) = flow(Sᶜ,S)`
(`Arlib.MarkovChains.IsReversible`), so the summand at a set of mass above `1/2` equals the
summand at its complement, which is already in the family.  Cutting at `1/2` — as
`Arlib.MarkovChains.conductance` does — therefore loses nothing and keeps the definition
uniform with the rest of `Conductance.lean`. -/
noncomputable def conductanceS (P : Kernel Ω Ω) (pi : Measure Ω) (s : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ S ∈ MidSets pi s, conductanceSOn P pi s S

/-- Membership in `MidSets`, unfolded. -/
theorem mem_midSets_iff {pi : Measure Ω} {s : ℝ≥0∞} {S : Set Ω} :
    S ∈ MidSets pi s ↔ MeasurableSet S ∧ s < pi S ∧ pi S ≤ 1 / 2 := Iff.rfl

/-- Discounting the denominator can only increase the quotient:
`Φ(S) ≤ Φ_s(S)` for every set and every `s`. -/
theorem conductanceOn_le_conductanceSOn (P : Kernel Ω Ω) (pi : Measure Ω) (s : ℝ≥0∞)
    (S : Set Ω) : conductanceOn P pi S ≤ conductanceSOn P pi s S := by
  rw [conductanceOn, conductanceSOn]
  gcongr
  exact tsub_le_self

/-- **`Φ ≤ Φ_s`.**  A lower bound on the ordinary conductance is a lower bound on the
`s`-conductance, with no loss.

This is the formal content of the sentence in §1 of *Hit-and-Run from a Corner* that
distinguishes hit-and-run from the ball walk: Theorem 4.2 bounds the conductance of *every*
subset, so the `s`-discount buys nothing and is not needed.  (For the ball walk the
inequality is still true but useless, because the left-hand side is `0`.) -/
theorem conductance_le_conductanceS (P : Kernel Ω Ω) (pi : Measure Ω) (s : ℝ≥0∞) :
    conductance P pi ≤ conductanceS P pi s := by
  refine le_iInf₂ fun S hS => ?_
  have hpos : 0 < pi S :=
    lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ s from zero_le) hS.2.1
  exact (conductance_le_conductanceOn P pi hS.1 hpos hS.2.2).trans
    (conductanceOn_le_conductanceSOn P pi s S)

/-- To bound `Φ_s` from below it suffices to bound the ordinary conductance of every
measurable set of mass in `(0, 1/2]`. -/
theorem le_conductanceS (P : Kernel Ω Ω) (pi : Measure Ω) (s : ℝ≥0∞) {c : ℝ≥0∞}
    (h : ∀ S : Set Ω, MeasurableSet S → 0 < pi S → pi S ≤ 1 / 2 → c ≤ conductanceOn P pi S) :
    c ≤ conductanceS P pi s :=
  (le_conductance P pi h).trans (conductance_le_conductanceS P pi s)

/-! ## Exceptional starts

Theorem 1.1 does not assume the start `σ` is warm.  It assumes `σ` is warm *off an
exceptional set* `S` of `σ`-mass at most `ε/2`.  §5 of the paper handles this in one
sentence — "we think of a random point of `K` as being generated with probability `1 − ε/2`
from a distribution `μ₀` that is `(2M)`-warm with respect to `π_K` and with probability
`ε/2` from some other distribution" — and this section is that sentence, proved.

The construction is `restrictOff σ S`, the law of `σ` conditioned on `Sᶜ`.  Two facts about
it are needed and both are sharp: it is `2M`-warm (`isWarm_restrictOff`), and it is within
total variation `σ(S)` — not `2σ(S)` — of `σ` itself (`tvLe_restrictOff`). -/

section Exceptional

variable {sigma pi : Measure Ω} {S : Set Ω}

/-- **The start, conditioned on avoiding the exceptional set**: `σ` restricted to `Sᶜ` and
renormalised.  This is the paper's `μ₀`. -/
noncomputable def restrictOff (sigma : Measure Ω) (S : Set Ω) : Measure Ω :=
  (sigma Sᶜ)⁻¹ • sigma.restrict Sᶜ

/-- The mass `restrictOff σ S` gives a measurable event. -/
theorem restrictOff_apply (sigma : Measure Ω) {S A : Set Ω} (hA : MeasurableSet A) :
    restrictOff sigma S A = sigma (A \ S) / sigma Sᶜ := by
  rw [restrictOff, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
    ENNReal.div_eq_inv_mul, Set.sdiff_eq]

/-- **Half the mass survives.**  If the exceptional set carries at most half the mass then
its complement carries at least half.  (Stated for a probability measure; the `1/2` is what
turns the `M`-warmness of `σ` off `S` into the `2M`-warmness of `restrictOff σ S`.) -/
theorem half_le_measure_compl [IsProbabilityMeasure sigma] (hSm : MeasurableSet S)
    (hS : sigma S ≤ 1 / 2) : 1 / 2 ≤ sigma Sᶜ := by
  have htot : sigma S + sigma Sᶜ = 1 := by
    rw [measure_add_measure_compl hSm, measure_univ]
  have hstep : (1 : ℝ≥0∞) / 2 + 1 / 2 ≤ 1 / 2 + sigma Sᶜ := by
    calc (1 : ℝ≥0∞) / 2 + 1 / 2 = 1 := ENNReal.add_halves 1
      _ = sigma S + sigma Sᶜ := htot.symm
      _ ≤ 1 / 2 + sigma Sᶜ := by gcongr
  exact ENNReal.le_of_add_le_add_left (by simp) hstep

/-- `restrictOff σ S` is a probability measure, as soon as `Sᶜ` carries positive mass. -/
theorem isProbabilityMeasure_restrictOff [IsProbabilityMeasure sigma] (hSm : MeasurableSet S)
    (hS : sigma S ≤ 1 / 2) : IsProbabilityMeasure (restrictOff sigma S) := by
  have hpos : 0 < sigma Sᶜ := lt_of_lt_of_le (by norm_num) (half_le_measure_compl hSm hS)
  refine ⟨?_⟩
  rw [restrictOff_apply sigma MeasurableSet.univ,
    (Set.compl_eq_univ_sdiff S).symm,
    ENNReal.div_self hpos.ne' (measure_ne_top sigma _)]

/-- **`restrictOff` preserves warmness, at twice the constant.**  If `σ(A ∖ S) ≤ M·π(A)` for
every measurable `A` and `S` carries at most half the mass, then the conditioned start is
`2M`-warm.

This is the paper's `(2M)`-warm `μ₀`; the `2` is `1/(1 − ε/2)` bounded using `ε ≤ 1`, a step
§5 performs silently (see the module docstring, *Errors in the paper*, item 4). -/
theorem isWarm_restrictOff [IsProbabilityMeasure sigma] (hSm : MeasurableSet S)
    (hS : sigma S ≤ 1 / 2) {M : ℝ≥0∞}
    (hdom : ∀ A : Set Ω, MeasurableSet A → sigma (A \ S) ≤ M * pi A) :
    IsWarm (2 * M) (restrictOff sigma S) pi := by
  intro A hA
  have hhalf : 1 / 2 ≤ sigma Sᶜ := half_le_measure_compl hSm hS
  calc restrictOff sigma S A = sigma (A \ S) / sigma Sᶜ := restrictOff_apply sigma hA
    _ ≤ sigma (A \ S) / (1 / 2) := by gcongr
    _ = 2 * sigma (A \ S) := by
        rw [ENNReal.div_eq_inv_mul]
        norm_num
    _ ≤ 2 * (M * pi A) := by gcongr; exact hdom A hA
    _ = 2 * M * pi A := (mul_assoc _ _ _).symm

/-- **Conditioning on `Sᶜ` moves the law by at most `σ(S)`.**

The naive estimate — `σ` and `restrictOff σ S` differ by the mass on `S` plus the
renormalisation — gives `2σ(S)`.  The sharp constant `σ(S)` comes from
`σ(A ∩ Sᶜ) ≤ σ(Sᶜ)`: the renormalisation inflates a set of mass `x ≤ a := σ(Sᶜ)` to `x/a`,
and `x/a − x = x(1−a)/a ≤ (1−a) = σ(S)`.  Getting `σ(S)` rather than `2σ(S)` is what makes
the paper's `ε/2 + ε/2` bookkeeping close exactly.

Proved through `Arlib.tvLe_of_forall_le`, so only one direction has to be checked; it is
stated without any `ℝ≥0∞` subtraction by using `σ(S) + σ(Sᶜ) = 1` directly. -/
theorem tvLe_restrictOff [IsProbabilityMeasure sigma] (hSm : MeasurableSet S)
    (hS : sigma S ≤ 1 / 2) :
    Arlib.TVLe sigma (restrictOff sigma S) (sigma S) := by
  have hpos : 0 < sigma Sᶜ := lt_of_lt_of_le (by norm_num) (half_le_measure_compl hSm hS)
  have htot : sigma S + sigma Sᶜ = 1 := by
    rw [measure_add_measure_compl hSm, measure_univ]
  have := isProbabilityMeasure_restrictOff hSm hS
  refine (Arlib.tvLe_of_forall_le fun A hA => ?_).symm
  rw [restrictOff_apply sigma hA,
    ENNReal.div_le_iff hpos.ne' (measure_ne_top sigma _)]
  have hxa : sigma (A \ S) ≤ sigma Sᶜ := measure_mono (by rw [Set.sdiff_eq_compl_inter]; exact
    Set.inter_subset_left)
  have hxA : sigma (A \ S) ≤ sigma A := measure_mono Set.sdiff_subset
  calc sigma (A \ S) = sigma (A \ S) * (sigma S + sigma Sᶜ) := by rw [htot, mul_one]
    _ = sigma (A \ S) * sigma S + sigma (A \ S) * sigma Sᶜ := by ring
    _ ≤ sigma Sᶜ * sigma S + sigma A * sigma Sᶜ := by gcongr
    _ = (sigma A + sigma S) * sigma Sᶜ := by ring

/-- **The exceptional-set split.**  The chain started from `σ` tracks the chain started from
the conditioned law `restrictOff σ S`, at a cost of exactly `σ(S)`.

Only the kernel data-processing inequality (`Arlib.MarkovChains.tvLe_iterate`, from
`Warmness.lean`) and the triangle inequality are used, so this holds for *every* Markov
kernel and every number of steps. -/
theorem tvLe_iterate_of_exceptional {P : Kernel Ω Ω} [IsMarkovKernel P]
    [IsProbabilityMeasure sigma] (hSm : MeasurableSet S) (hS : sigma S ≤ 1 / 2) {b : ℝ≥0∞}
    {m : ℕ} (hmix : Arlib.TVLe (iterate P (restrictOff sigma S) m) pi b) :
    Arlib.TVLe (iterate P sigma m) pi (sigma S + b) :=
  (tvLe_iterate P (tvLe_restrictOff hSm hS) m).trans hmix

end Exceptional

/-! ## From a decay rate to a deadline

`MixingFromConductance.lean` already turns a geometric decay `M(1−c)^t` into a step count
(`mixingTime`, `mul_pow_le_of_mixingTime_le`).  What is added here is the specific
Lovász–Simonovits shape that §5 of the paper needs — start `2M`-warm, target accuracy `ε/2`
— and the observation that the resulting threshold is exactly `log(8M/ε²)/Φ²`, with no
stray square roots. -/

/-- `log (√(2M) / (ε/2)) = log(8M/ε²) / 2`.  Both sides are the logarithm of the same
positive number, since `(2√(2M)/ε)² = 8M/ε²`. -/
theorem log_sqrt_two_mul_div {M eps : ℝ} (hM : 0 < M) (heps : 0 < eps) :
    Real.log (Real.sqrt (2 * M) / (eps / 2)) = Real.log (8 * M / eps ^ 2) / 2 := by
  have hsq : 8 * M / eps ^ 2 = (Real.sqrt (2 * M) / (eps / 2)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * M)]
    field_simp
    ring
  rw [hsq, Real.log_pow]
  push_cast
  ring

/-- **The Lovász–Simonovits deadline**: `log(8M/ε²) / Φ²`.

This is the number of steps after which a `2M`-warm start has come within `ε/2` of
stationarity, under the decay bound `√(2M)(1 − Φ²/2)^t`.  The `ε/2` — rather than `ε` — is
deliberate: the other `ε/2` is spent on the exceptional set. -/
noncomputable def lsThreshold (M phi eps : ℝ) : ℝ :=
  Real.log (8 * M / eps ^ 2) / phi ^ 2

/-- **`√(2M)·(1 − Φ²/2)^m ≤ ε/2` past the deadline.**  Pure real analysis; the content is
`mul_pow_le_of_mixingTime_le` of `MixingFromConductance.lean` plus the identification
`log_sqrt_two_mul_div` of the two spellings of the threshold. -/
theorem sqrt_mul_pow_le_of_lsThreshold_le {M phi eps : ℝ} (hM : 1 ≤ M) (hphi0 : 0 < phi)
    (hphi1 : phi ≤ 1) (heps : 0 < eps) {m : ℕ} (hm : lsThreshold M phi eps ≤ (m : ℝ)) :
    Real.sqrt (2 * M) * (1 - phi ^ 2 / 2) ^ m ≤ eps / 2 := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hphine : phi ≠ 0 := ne_of_gt hphi0
  have hc0 : 0 < phi ^ 2 / 2 := by positivity
  have hc1 : phi ^ 2 / 2 ≤ 1 := by nlinarith
  have hsq : 0 < Real.sqrt (2 * M) := Real.sqrt_pos.2 (by linarith)
  refine mul_pow_le_of_mixingTime_le hsq hc0 hc1 (by positivity) ?_
  rw [mixingTime, Nat.ceil_le, log_sqrt_two_mul_div hMpos heps]
  have hrw : Real.log (8 * M / eps ^ 2) / 2 / (phi ^ 2 / 2)
      = Real.log (8 * M / eps ^ 2) / phi ^ 2 := by
    field_simp
  rw [hrw]
  exact hm

/-! ## Theorem 1.1, for an arbitrary Markov chain

The paper's §5, with its two external inputs made into explicit binders: the conductance
bound `hcond` (its Theorem 4.2) and the Lovász–Simonovits decay bound `hLS` (Corollary 1.5
of [11]).  Everything between them is proved. -/

/-- **Theorem 1.1 of Lovász–Vempala, abstractly.**

Let `P` be a Markov kernel with stationary measure `pi` and conductance at least `phi`.  Let
the start `sigma` be dominated by `M·pi` off a measurable exceptional set `S` of `sigma`-mass
at most `ε/2`.  Then after `lsThreshold M phi ε = log(8M/ε²)/phi²` steps the chain is within
total variation `ε` of `pi`.

The hypothesis `hdom` is stated with `pi A` — not `pi (A \ S)` — on the right, which is the
*weaker* assumption of the two and hence the stronger theorem; a caller holding
`sigma (A \ S) ≤ M · pi (A \ S)` (the shape of the Radon–Nikodym hypothesis in the paper and
in `Ttc.HitAndRunTheorem11Input`) gets `hdom` by monotonicity of `pi`.

`hLS` is Corollary 1.5 of Lovász–Simonovits (1993) and is **not proved anywhere in this
repository**; see the module docstring, `§ What is assumed`, including the two-line
counterexample showing that it is false without a laziness or spectral hypothesis. -/
theorem tvLe_iterate_of_exceptional_of_ls {P : Kernel Ω Ω} [IsMarkovKernel P]
    {sigma pi : Measure Ω} [IsProbabilityMeasure sigma] {S : Set Ω}
    {M phi eps : ℝ} (hM : 1 ≤ M) (hphi0 : 0 < phi) (hphi1 : phi ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set Ω, MeasurableSet A → sigma (A \ S) ≤ ENNReal.ofReal M * pi A)
    (hcond : ENNReal.ofReal phi ≤ conductance P pi)
    (hLS : ∀ ph W : ℝ, 0 < ph → ph ≤ 1 → 1 ≤ W → ENNReal.ofReal ph ≤ conductance P pi →
      ∀ mu : Measure Ω, IsProbabilityMeasure mu → Arlib.IsWarm (ENNReal.ofReal W) mu pi →
        ∀ t : ℕ, Arlib.TVLe (iterate P mu t) pi
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t)))
    {m : ℕ} (hm : lsThreshold M phi eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate P sigma m) pi (ENNReal.ofReal eps) := by
  have hhalfR : eps / 2 ≤ 1 / 2 := by linarith
  have hShalf : sigma S ≤ 1 / 2 := by
    refine hS.trans ?_
    calc ENNReal.ofReal (eps / 2) ≤ ENNReal.ofReal (1 / 2) :=
          ENNReal.ofReal_le_ofReal hhalfR
      _ = 1 / 2 := by
          rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
  have hprob := isProbabilityMeasure_restrictOff hSm hShalf
  have hwarm : Arlib.IsWarm (ENNReal.ofReal (2 * M)) (restrictOff sigma S) pi := by
    have h := isWarm_restrictOff (pi := pi) hSm hShalf hdom
    rwa [ENNReal.ofReal_mul (by norm_num), show ENNReal.ofReal (2 : ℝ) = 2 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num]
  have hdecay := hLS phi (2 * M) hphi0 hphi1 (by linarith) hcond _ hprob hwarm m
  have hnum : Real.sqrt (2 * M) * (1 - phi ^ 2 / 2) ^ m ≤ eps / 2 :=
    sqrt_mul_pow_le_of_lsThreshold_le hM hphi0 hphi1 heps0 hm
  have hdecay' : Arlib.TVLe (iterate P (restrictOff sigma S) m) pi (ENNReal.ofReal (eps / 2)) :=
    hdecay.mono (ENNReal.ofReal_le_ofReal hnum)
  refine (tvLe_iterate_of_exceptional hSm hShalf hdecay').mono ?_
  calc sigma S + ENNReal.ofReal (eps / 2)
      ≤ ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) := by gcongr
    _ = ENNReal.ofReal (eps / 2 + eps / 2) := (ENNReal.ofReal_add (by linarith) (by linarith)).symm
    _ = ENNReal.ofReal eps := by norm_num

/-! ## The `s`-conductance route to the same deadline

§5 of *Hit-and-Run from a Corner* does not use `s`-conductance (see the module docstring),
but the `s`-conductance form of the Lovász–Simonovits theorem gives the *same* logarithmic
dependence by a different route, and it is the form a chain whose small sets misbehave — the
ball walk — is forced to use.  It is recorded here in full because it costs little once the
warm-start bookkeeping is in place, and because `conductance_le_conductanceS` says a
hit-and-run conductance bound feeds it with no loss.

The Lovász–Simonovits statement (RSA 1993, Corollary 1.5, `s`-conductance form) is

    d_TV(σ_m, π)  ≤  H_s  +  (H_s / s) · (1 − Φ_s²/2)^m,

where `H_s = sup { |σ(A) − π(A)| : π(A) ≤ s }`.  What is proved here is everything around it:
`H_s ≤ M·s` for an `M`-warm start (`smallSetDiscrepancy_of_isWarm`), the choice
`s = ε/(2M)` that turns `H_s` into `ε/2`, and the arithmetic that makes the residual
`M(1 − Φ_s²/2)^m` at most `ε/2` after `2 log(2M/ε)/Φ_s²` steps.  The displayed inequality
itself is the binder `hLSs`. -/

/-- `ENNReal.ofReal (1/2 : ℝ) = 1/2`.  Used repeatedly below to convert the real threshold
`ε/2` into the `ℝ≥0∞` cut-off of `Conductance.lean`. -/
theorem ofReal_one_half : ENNReal.ofReal ((1 : ℝ) / 2) = (1 : ℝ≥0∞) / 2 := by
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The **`s`-discrepancy** of `mu` relative to `pi`: on every set of `pi`-mass at most `s`
the two measures differ by at most `H`.  This is `H_s ≤ H` in the notation of
Lovász–Simonovits, stated as a bound rather than as a supremum for the same reason
`Arlib.TVLe` is (`Arlib/Probability/TV.lean`, module docstring). -/
def SmallSetDiscrepancy (mu pi : Measure Ω) (s H : ℝ≥0∞) : Prop :=
  ∀ A : Set Ω, MeasurableSet A → pi A ≤ s → mu A ≤ pi A + H ∧ pi A ≤ mu A + H

/-- **A warm start has small `s`-discrepancy**: an `M`-warm `mu` satisfies `H_s ≤ M·s`.

This is the whole reason the `s`-conductance route also gives a *logarithmic* dependence on
`M`: `H_s` is proportional to `s`, so choosing `s = ε/(2M)` makes the additive term `ε/2`
while only costing `log M` in the exponent. -/
theorem smallSetDiscrepancy_of_isWarm {mu pi : Measure Ω} {M s : ℝ≥0∞} (hM : 1 ≤ M)
    (h : Arlib.IsWarm M mu pi) : SmallSetDiscrepancy mu pi s (M * s) := by
  intro A hA hAs
  refine ⟨?_, ?_⟩
  · calc mu A ≤ M * pi A := h A hA
      _ ≤ M * s := by gcongr
      _ ≤ pi A + M * s := le_add_self
  · calc pi A ≤ s := hAs
      _ = 1 * s := (one_mul s).symm
      _ ≤ M * s := by gcongr
      _ ≤ mu A + M * s := le_add_self

/-- **The `s`-conductance deadline**: `2·log(2M/ε) / Φ_s²`. -/
noncomputable def lsThresholdS (M phi eps : ℝ) : ℝ :=
  2 * Real.log (2 * M / eps) / phi ^ 2

/-- **`M·(1 − Φ_s²/2)^m ≤ ε/2` past the `s`-conductance deadline.** -/
theorem mul_pow_le_of_lsThresholdS_le {M phi eps : ℝ} (hM : 1 ≤ M) (hphi0 : 0 < phi)
    (hphi1 : phi ≤ 1) (heps : 0 < eps) {m : ℕ} (hm : lsThresholdS M phi eps ≤ (m : ℝ)) :
    M * (1 - phi ^ 2 / 2) ^ m ≤ eps / 2 := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hphine : phi ≠ 0 := ne_of_gt hphi0
  have hc0 : 0 < phi ^ 2 / 2 := by positivity
  have hc1 : phi ^ 2 / 2 ≤ 1 := by nlinarith
  refine mul_pow_le_of_mixingTime_le hMpos hc0 hc1 (by positivity) ?_
  rw [mixingTime, Nat.ceil_le, show M / (eps / 2) = 2 * M / eps by field_simp]
  have hrw : Real.log (2 * M / eps) / (phi ^ 2 / 2)
      = 2 * Real.log (2 * M / eps) / phi ^ 2 := by field_simp
  rw [hrw]
  exact hm

/-- **Mixing from `s`-conductance, for a warm start.**

Let `P` be a Markov kernel with stationary `pi` whose `s`-conductance at `s = ε/(2M)` is at
least `phi`, and let `sigma` be `M`-warm.  Then after `2 log(2M/ε)/phi²` steps the chain is
within total variation `ε` of `pi`.

`hLSs` is the Lovász–Simonovits bound `d_TV(σ_m,π) ≤ H_s + (H_s/s)(1 − Φ_s²/2)^m` — it is a
binder, not a theorem of this repository.  Everything else is proved: the passage from
warmness to `H_s ≤ M s`, the choice of `s`, and the step count.

Note the shape of the answer: the deadline is `O(Φ_s⁻² log(M/ε))`, *logarithmic* in `M` and
`1/ε`.  Together with `conductance_le_conductanceS` — which says that a conductance bound
valid for **every** subset, as Theorem 4.2 supplies, is an `Φ_s` bound with no loss at any
`s` — this is a second, independent route to Theorem 1.1's logarithmic dependence. -/
theorem tvLe_iterate_of_sConductance {P : Kernel Ω Ω} [IsMarkovKernel P]
    {sigma pi : Measure Ω} [IsProbabilityMeasure sigma] {M phi eps : ℝ}
    (hM : 1 ≤ M) (hphi0 : 0 < phi) (hphi1 : phi ≤ 1) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) sigma pi)
    (hcond : ENNReal.ofReal phi ≤ conductanceS P pi (ENNReal.ofReal (eps / (2 * M))))
    (hLSs : ∀ (s H : ℝ≥0∞) (ph : ℝ), 0 < ph → ph ≤ 1 → 0 < s → s ≤ 1 / 2 →
        ENNReal.ofReal ph ≤ conductanceS P pi s →
        ∀ mu : Measure Ω, IsProbabilityMeasure mu → SmallSetDiscrepancy mu pi s H →
        ∀ t : ℕ, Arlib.TVLe (iterate P mu t) pi
          (H + H / s * ENNReal.ofReal ((1 - ph ^ 2 / 2) ^ t)))
    {m : ℕ} (hm : lsThresholdS M phi eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate P sigma m) pi (ENNReal.ofReal eps) := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hspos : (0 : ℝ) < eps / (2 * M) := by positivity
  set s : ℝ≥0∞ := ENNReal.ofReal (eps / (2 * M)) with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact (ENNReal.ofReal_pos.2 hspos).ne'
  have hstop : s ≠ ⊤ := by rw [hs]; exact ENNReal.ofReal_ne_top
  have hshalf : s ≤ 1 / 2 := by
    rw [hs, ← ofReal_one_half]
    exact ENNReal.ofReal_le_ofReal (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hM1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal M := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hM
  have hdisc : SmallSetDiscrepancy sigma pi s (ENNReal.ofReal M * s) :=
    smallSetDiscrepancy_of_isWarm hM1 hwarm
  have hHalf : ENNReal.ofReal M * s = ENNReal.ofReal (eps / 2) := by
    rw [hs, ← ENNReal.ofReal_mul hMpos.le]
    congr 1
    field_simp
  have hbound := hLSs s (ENNReal.ofReal M * s) phi hphi0 hphi1 (pos_iff_ne_zero.2 hs0) hshalf
    hcond sigma inferInstance hdisc m
  refine hbound.mono ?_
  have hdiv : ENNReal.ofReal M * s / s = ENNReal.ofReal M :=
    ENNReal.mul_div_cancel_right hs0 hstop
  rw [hdiv, hHalf]
  have hpow : (0 : ℝ) ≤ (1 - phi ^ 2 / 2) ^ m := by
    have : (0 : ℝ) ≤ 1 - phi ^ 2 / 2 := by nlinarith
    positivity
  calc ENNReal.ofReal (eps / 2) + ENNReal.ofReal M * ENNReal.ofReal ((1 - phi ^ 2 / 2) ^ m)
      = ENNReal.ofReal (eps / 2) + ENNReal.ofReal (M * (1 - phi ^ 2 / 2) ^ m) := by
        rw [ENNReal.ofReal_mul hMpos.le]
    _ ≤ ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) := by
        gcongr
        exact mul_pow_le_of_lsThresholdS_le hM hphi0 hphi1 heps0 hm
    _ = ENNReal.ofReal (eps / 2 + eps / 2) :=
        (ENNReal.ofReal_add (by linarith) (by linarith)).symm
    _ = ENNReal.ofReal eps := by norm_num

/-! ### A non-vacuity witness for the `hLSs` binder, and a scope caveat on [11]

**The Lovász–Simonovits `s`-conductance bound as usually quoted is false on a space with
atoms.**  Counterexample, on `Bool` with `pi = piHalf`: take `P = Kernel.const Bool piHalf`
(whose conductance `conductance_const_piHalf` computes to `1/2`), `s = 1/4`, `H = 0`,
`ph = 1/2`, `mu = Measure.dirac true`.

* the premise `ofReal (1/2) ≤ conductanceS P piHalf (1/4)` holds — the only admissible sets
  are the two singletons, each with ratio `flow/(π(S) − s) = (1/4)/(1/4) = 1`;
* `SmallSetDiscrepancy (dirac true) piHalf (1/4) 0` holds **vacuously**, because the only
  measurable set of `piHalf`-mass at most `1/4` is `∅`;
* but the conclusion at `t = 0` reads `TVLe (dirac true) piHalf (0 + 0/(1/4) · 1)`, i.e.
  `TVLe (dirac true) piHalf 0`, which by `Arlib.TVLe.eq_of_zero` forces
  `dirac true = piHalf`.  False.

The reason is that Lovász–Simonovits work on `ℝⁿ` with atomless `π`, where "`μ` agrees with
`π` on every set of mass at most `s`" upgrades to `μ = π` by chopping an arbitrary set into
`⌈1/s⌉` pieces of mass at most `s`; with atoms that upgrade fails and `H_s` can be `0` while
`d_TV(μ, π) = 1/2`.  This is a scope caveat on Corollary 1.5 of **[11]**, not on
Lovász–Vempala, and the hit-and-run application is atomless (`Arlib.uniformOn volume K` on
`ℝⁿ`), so it does not bite there.  It is recorded because it is exactly the reason `hLSs`
must be a `∀`-binder and never a `def`.

What *is* machine-checked below is that `hLSs` is not empty: the identity kernel discharges
it on `Bool`.  Its `s`-conductance is `0` at every `s < 1/2` (nothing ever leaves a set),
which kills the premise; and at `s = 1/2` every proper subset of `Bool` is already covered by
the discrepancy hypothesis, so the conclusion follows from it directly. -/

/-- **One step of the identity kernel leaves the law where it is.** -/
theorem step_deterministic_id (mu : Measure Ω) :
    step (Kernel.deterministic (id : Ω → Ω) measurable_id) mu = mu := by
  ext S hS
  rw [step_apply _ _ hS]
  have hpt : ∀ x : Ω,
      (Kernel.deterministic (id : Ω → Ω) measurable_id : Kernel Ω Ω) x S
        = S.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    rw [Kernel.deterministic_apply, Measure.dirac_apply' _ hS]
    rfl
  simp only [hpt]
  rw [lintegral_indicator hS, setLIntegral_one]

/-- **The identity chain never moves.** -/
theorem iterate_deterministic_id (mu : Measure Ω) (t : ℕ) :
    iterate (Kernel.deterministic (id : Ω → Ω) measurable_id) mu t = mu := by
  induction t with
  | zero => rfl
  | succ t ih => rw [iterate_succ, ih, step_deterministic_id]

/-- **Nothing ever escapes a set under the identity kernel**: every ergodic flow out of a
measurable set into its complement is `0`. -/
theorem flow_deterministic_id_compl (pi : Measure Ω) {S : Set Ω} (hS : MeasurableSet S) :
    flow (Kernel.deterministic (id : Ω → Ω) measurable_id) pi S Sᶜ = 0 := by
  have hle : ∫⁻ x in S,
        (Kernel.deterministic (id : Ω → Ω) measurable_id : Kernel Ω Ω) x Sᶜ ∂pi
      ≤ ∫⁻ _x in S, (0 : ℝ≥0∞) ∂pi := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict hS] with x hx
    rw [Kernel.deterministic_apply, Measure.dirac_apply' _ hS.compl]
    simp [hx]
  simpa [flow] using hle

/-- The identity kernel on `Bool` has `s`-conductance `0` for every `s < 1/2`: the singleton
`{true}` is admissible and leaks nothing. -/
theorem conductanceS_deterministic_id_piHalf {s : ℝ≥0∞} (hs : s < 1 / 2) :
    conductanceS (Kernel.deterministic (id : Bool → Bool) measurable_id) piHalf s = 0 := by
  refine le_antisymm ?_ zero_le
  refine (iInf₂_le ({true} : Set Bool)
    ⟨measurableSet_singleton true, by rw [piHalf_singleton]; exact hs,
      (piHalf_singleton true).le⟩).trans_eq ?_
  rw [conductanceSOn, flow_deterministic_id_compl _ (measurableSet_singleton true),
    ENNReal.zero_div]

/-- **Non-vacuity witness for `hLSs` (`CLAUDE.md` §11).**  The identity kernel on `Bool`
satisfies the Lovász–Simonovits `s`-conductance binder in full. -/
theorem lsS_deterministic_id :
    ∀ (s H : ℝ≥0∞) (ph : ℝ), 0 < ph → ph ≤ 1 → 0 < s → s ≤ 1 / 2 →
      ENNReal.ofReal ph
        ≤ conductanceS (Kernel.deterministic (id : Bool → Bool) measurable_id) piHalf s →
      ∀ mu : Measure Bool, IsProbabilityMeasure mu → SmallSetDiscrepancy mu piHalf s H →
      ∀ t : ℕ, Arlib.TVLe
        (iterate (Kernel.deterministic (id : Bool → Bool) measurable_id) mu t) piHalf
        (H + H / s * ENNReal.ofReal ((1 - ph ^ 2 / 2) ^ t)) := by
  intro s H ph hph0 hph1 _ hshalf hcond mu hmu hdisc t
  haveI := hmu
  rcases lt_or_eq_of_le hshalf with hlt | heq
  · exfalso
    rw [conductanceS_deterministic_id_piHalf hlt, le_zero_iff, ENNReal.ofReal_eq_zero] at hcond
    linarith
  · rw [iterate_deterministic_id]
    refine Arlib.TVLe.mono ?_ le_self_add
    intro A hA
    by_cases hu : A = Set.univ
    · subst hu
      rw [measure_univ, measure_univ]
      exact ⟨le_self_add, le_self_add⟩
    · refine hdisc A hA ?_
      obtain ⟨b, hb⟩ : ∃ b : Bool, b ∉ A := by
        by_contra h
        exact hu (Set.eq_univ_of_forall fun x => not_not.1 fun hx => h ⟨x, hx⟩)
      have hsub : A ⊆ ({b} : Set Bool)ᶜ := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl
        exact hb hx
      calc piHalf A ≤ piHalf ({b} : Set Bool)ᶜ := measure_mono hsub
        _ = 1 / 2 := piHalf_compl_singleton b
        _ = s := heq.symm

/-! ## A non-vacuity witness for the `hLS` binder (`CLAUDE.md` §11)

A theorem whose hypothesis nothing satisfies proves nothing.  The instantly mixing kernel
`Kernel.const Ω pi` — resample from `pi` at every step — satisfies the Lovász–Simonovits
binder `hLS` exactly, at every `phi` and every warmness `W`, and
`Arlib.MarkovChains.conductance_const_piHalf` computes its conductance on the two-point space
to be `1/2`.  So `hLS` is inhabited, and the abstract Theorem 1.1 below is not vacuous.

Contrast the swap kernel `P x = dirac (!x)` on `Bool`, recorded in the module docstring: it is
reversible with respect to `piHalf` and has conductance `1`, yet `hLS` **fails** for it.  The
binder is therefore a genuine restriction, not a tautology — which is precisely why it must be
a binder and not a `def`. -/

/-- **The instantly mixing kernel discharges `hLS`.**  At `t = 0` the bound is `√W ≥ 1` and
`Arlib.tvLe_one` suffices; at `t ≥ 1` the law is exactly `pi`. -/
theorem ls_const (pi : Measure Ω) [IsProbabilityMeasure pi] :
    ∀ ph W : ℝ, 0 < ph → ph ≤ 1 → 1 ≤ W →
      ENNReal.ofReal ph ≤ conductance (Kernel.const Ω pi) pi →
      ∀ mu : Measure Ω, IsProbabilityMeasure mu → Arlib.IsWarm (ENNReal.ofReal W) mu pi →
        ∀ t : ℕ, Arlib.TVLe (iterate (Kernel.const Ω pi) mu t) pi
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t)) := by
  intro ph W _ _ hW _ mu hmu _ t
  haveI := hmu
  cases t with
  | zero =>
      have hsq : (1 : ℝ) ≤ Real.sqrt W := by
        have h := Real.sqrt_le_sqrt hW
        rwa [Real.sqrt_one] at h
      rw [iterate_zero]
      refine (Arlib.tvLe_one mu pi).mono ?_
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal (by simpa using hsq)
  | succ k =>
      rw [iterate_succ, step_const_eq]
      exact (Arlib.TVLe.refl pi).mono zero_le

/-! ## Theorem 1.1 for hit-and-run

The kernel is `Arlib.MarkovChains.hitAndRun K` and the target is `Arlib.uniformOn volume K`,
so the statement below is about the *real* objects, not a surrogate (`CLAUDE.md` §11). -/

/-- **The deadline of Theorem 1.1, at the constant this development actually obtains**:

    2⁵⁶ · n² · (R²/r²) · log(8M/ε²).

The paper prints `10¹⁰ · n² · (R²/r²) · ln(M/ε)`.  That number is **not** derivable from the
paper's own Theorem 4.2 — see the module docstring, *Errors in the paper*, item 1 — and it is
not derivable here either.  `2⁵⁶ ≈ 7.2 × 10¹⁶`, and `log(8M/ε²) ≤ log 8 + 2 log(M/ε)` for
`M ≥ 1`, `0 < ε ≤ 1`, so this deadline is about `1.4 × 10¹⁷ n²(R²/r²) log(M/ε)` in the paper's
shape.  Roughly a factor `10⁵` of the discrepancy is the paper's own arithmetic and a factor
`2⁶ = 64` is this repository's `2²⁷`-versus-`2²⁴` loss in Theorem 4.2 (`HitAndRunConductance.lean`,
which traces that in turn to a single factor `10` in Lemma 3.3). -/
noncomputable def lvThreshold (n : ℕ) (r R M eps : ℝ) : ℝ :=
  2 ^ 56 * (n : ℝ) ^ 2 * R ^ 2 / r ^ 2 * Real.log (8 * M / eps ^ 2)

/-- `lvThreshold` is `lsThreshold` at `phi = r/(2²⁸·n·R)`: `1/phi² = 2⁵⁶ n² R²/r²`. -/
theorem lsThreshold_eq_lvThreshold {n : ℕ} {r R M eps : ℝ} (hn : 1 ≤ n) (hr : 0 < r)
    (hR : 0 < R) :
    lsThreshold M (r / (2 ^ 28 * (n : ℝ) * R)) eps = lvThreshold n r R M eps := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  rw [lsThreshold, lvThreshold, div_pow]
  field_simp

/-- **Theorem 1.1 of Lovász–Vempala, for hit-and-run**, at the deadline `lvThreshold`.

`K` need not even be convex for this statement to typecheck; convexity, the inball and the
circumball enter only through `hphi`, which is Theorem 4.2 in `r`/`R` form.  See the module
docstring for what `hphi` and `hLS` are and why they are binders.

`hdom` is the Radon–Nikodym hypothesis of the paper in measure form: away from the exceptional
set `S`, the start is dominated by `M` times the uniform target.  It is stated with
`uniformOn volume K A` rather than `uniformOn volume K (A \ S)` on the right, which is the
weaker hypothesis; a caller holding the `A \ S` form (as `Ttc.HitAndRunTheorem11Input` does)
obtains this one by monotonicity. -/
theorem tvLe_iterate_hitAndRun {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K A)
    (hphi : ENNReal.ofReal (r / (2 ^ 28 * (n : ℝ) * R))
      ≤ conductance (hitAndRun K) (Arlib.uniformOn volume K))
    (hLS : ∀ ph W : ℝ, 0 < ph → ph ≤ 1 → 1 ≤ W →
      ENNReal.ofReal ph ≤ conductance (hitAndRun K) (Arlib.uniformOn volume K) →
      ∀ mu : Measure (EuclideanSpace ℝ (Fin n)), IsProbabilityMeasure mu →
        Arlib.IsWarm (ENNReal.ofReal W) mu (Arlib.uniformOn volume K) →
        ∀ t : ℕ, Arlib.TVLe (iterate (hitAndRun K) mu t) (Arlib.uniformOn volume K)
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t)))
    {m : ℕ} (hm : lvThreshold n r R M eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (hitAndRun K) sigma m) (Arlib.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hphi0 : 0 < r / (2 ^ 28 * (n : ℝ) * R) := by positivity
  have hphi1 : r / (2 ^ 28 * (n : ℝ) * R) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  refine tvLe_iterate_of_exceptional_of_ls hM hphi0 hphi1 heps0 heps1 hSm hS hdom hphi hLS ?_
  rw [lsThreshold_eq_lvThreshold hn hr hR]
  exact hm

/-! ## Discharging `hphi` from Theorem 4.2, in the unit-inball case

`conductance_hitAndRun_ge` (`HitAndRunConductance.lean`) is Theorem 4.2 in the paper's own
normalisation: a body of diameter `D` containing a **unit** ball has conductance at least
`1/(2²⁷·n·D)`.  A body inside a ball of radius `R` has `D ≤ 2R`, so the same bound reads
`1/(2²⁸·n·R)` — which is exactly `hphi` at `r = 1`.

For general `r` this is the paper's "hit-and-run is invariant under a scaling of space", i.e.
the equivariance of `hitAndRun` under `x ↦ c·x`.  That equivariance is **not** proved in this
repository, so the general-`r` `hphi` remains a hypothesis; see the module docstring. -/

/-- **`hphi` at `r = 1`, from Theorem 4.2.**  The two `∀`-hypotheses are those of
`conductance_hitAndRun_ge` and are passed straight through: `hLem41` is the paper's Lemma 4.1
(one-step overlap, being proved in `HitAndRunOverlap.lean`) and `hIso` is the paper's
Theorem 2.1 (the weighted isoperimetric inequality) **in its corrected form**, carrying the
clause `∀ x ∈ K, h x ≤ 1/3` without which Theorem 2.1 is false (`Arlib.not_hIso_two`).
Nothing is added to them here beyond that correction, which is inherited verbatim from
`conductance_hitAndRun_ge`. -/
theorem ofReal_inv_le_conductance_hitAndRun_of_unitBall {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR : 0 < R) (hout : K ⊆ Metric.closedBall zout R)
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
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume K)) *
          min (Arlib.uniformOn volume K T₁) (Arlib.uniformOn volume K T₂)
        ≤ Arlib.uniformOn volume K ((K \ T₁) \ T₂)) :
    ENNReal.ofReal (1 / (2 ^ 28 * (n : ℝ) * R))
      ≤ conductance (hitAndRun K) (Arlib.uniformOn volume K) := by
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hout
  have hD : Metric.diam K ≤ 2 * R := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    have hx' := Metric.mem_closedBall.1 (hout hx)
    have hy' := Metric.mem_closedBall.1 (hout hy)
    calc dist x y ≤ dist x zout + dist zout y := dist_triangle x zout y
      _ = dist x zout + dist y zout := by rw [dist_comm zout y]
      _ ≤ R + R := by gcongr
      _ = 2 * R := by ring
  have h := conductance_hitAndRun_ge hn hKc hKcl hKm hKb hball hD hLem41 hIso
  rwa [show (2 : ℝ) ^ 27 * (n : ℝ) * (2 * R) = 2 ^ 28 * (n : ℝ) * R from by ring] at h

/-- **Theorem 1.1 for a body with a unit inball**, with `hphi` discharged.

This is the closest statement to `Ttc.HitAndRunTheorem11Input.mixing` that this development
reaches: it is about the real kernel and the real target, the exceptional-set hypothesis is
the paper's, and the only residual assumptions are `hLem41`, `hIso` (both from Theorem 4.2)
and `hLS` (Lovász–Simonovits Corollary 1.5).  `hIso` is Theorem 2.1 **corrected**: it carries
`∀ x ∈ K, h x ≤ 1/3`, without which the statement is false (`Arlib.not_hIso_two`) and this
theorem would be vacuous at `n = 2`, `K = [0,4]²`.

**It is at `r = 1` and at the deadline `lvThreshold n 1 R M eps = 2⁵⁶·n²·R²·log(8M/ε²)`, not
at the paper's `10¹⁰·n²·(R²/r²)·ln(M/ε)`.**  The two missing pieces are named in the module
docstring: scale equivariance of `hitAndRun` (for general `r`) and the paper's own arithmetic
error in the constant (for `10¹⁰`). -/
theorem tvLe_iterate_hitAndRun_unitBall {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    {z zout : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {R : ℝ} (hR1 : 1 ≤ R) (hout : K ⊆ Metric.closedBall zout R)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K A)
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
      (∫⁻ x, ENNReal.ofReal (h x) ∂(Arlib.uniformOn volume K)) *
          min (Arlib.uniformOn volume K T₁) (Arlib.uniformOn volume K T₂)
        ≤ Arlib.uniformOn volume K ((K \ T₁) \ T₂))
    (hLS : ∀ ph W : ℝ, 0 < ph → ph ≤ 1 → 1 ≤ W →
      ENNReal.ofReal ph ≤ conductance (hitAndRun K) (Arlib.uniformOn volume K) →
      ∀ mu : Measure (EuclideanSpace ℝ (Fin n)), IsProbabilityMeasure mu →
        Arlib.IsWarm (ENNReal.ofReal W) mu (Arlib.uniformOn volume K) →
        ∀ t : ℕ, Arlib.TVLe (iterate (hitAndRun K) mu t) (Arlib.uniformOn volume K)
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t)))
    {m : ℕ} (hm : lvThreshold n 1 R M eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (hitAndRun K) sigma m) (Arlib.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hR : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hphi := ofReal_inv_le_conductance_hitAndRun_of_unitBall hn hKc hKcl hKm hball hR hout
    hLem41 hIso
  refine tvLe_iterate_hitAndRun hn one_pos hR hR1 hM heps0 heps1 hSm hS hdom ?_ hLS hm
  simpa using hphi

/-! ### Axiom audit

`CLAUDE.md` §4: `#print axioms` is the only authoritative definition of done.  Every
declaration below must report exactly `[propext, Classical.choice, Quot.sound]`.  Note that
the two headline theorems carry their assumptions as `∀`-binders in their *types*, which
`#print axioms` does not see and cannot see — that is why the module docstring lists them, and
why `ls_const` (a witness that the `hLS` binder is satisfiable) is proved rather than
asserted. -/

section AxiomCheck

#print axioms conductance_le_conductanceS
#print axioms tvLe_restrictOff
#print axioms isWarm_restrictOff
#print axioms tvLe_iterate_of_exceptional
#print axioms sqrt_mul_pow_le_of_lsThreshold_le
#print axioms tvLe_iterate_of_exceptional_of_ls
#print axioms smallSetDiscrepancy_of_isWarm
#print axioms tvLe_iterate_of_sConductance
#print axioms lsS_deterministic_id
#print axioms ls_const
#print axioms lsThreshold_eq_lvThreshold
#print axioms tvLe_iterate_hitAndRun
#print axioms ofReal_inv_le_conductance_hitAndRun_of_unitBall
#print axioms tvLe_iterate_hitAndRun_unitBall

/-! ### A non-vacuity witness for the abstract Theorem 1.1 (`CLAUDE.md` §11)

`ls_const` shows the `hLS` binder alone is satisfiable.  The theorem below is stronger: it
exhibits a single concrete chain, start, exceptional set and parameter choice satisfying
**every** hypothesis of `tvLe_iterate_of_exceptional_of_ls` simultaneously, and derives its
conclusion *through that theorem* rather than directly.  So the abstract Theorem 1.1 is not
vacuously true over an unsatisfiable hypothesis set.

The chain is the uniform resampler on `Bool`, whose conductance
`conductance_const_piHalf` computes to exactly `1/2`; the start is `dirac true`, which is
`2`-warm with respect to `piHalf`; the exceptional set is empty. -/

/-- **Non-vacuity witness.**  Every hypothesis of `tvLe_iterate_of_exceptional_of_ls` is
satisfiable at once, with a non-trivial conclusion (`ε = 1/2 < 1`). -/
theorem tvLe_iterate_const_piHalf :
    Arlib.TVLe (iterate (Kernel.const Bool piHalf) (Measure.dirac true) 252) piHalf
      (ENNReal.ofReal (1 / 2)) := by
  have hofReal2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) = (1 : ℝ≥0∞) / 2 := by
    rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  refine tvLe_iterate_of_exceptional_of_ls (P := Kernel.const Bool piHalf)
    (sigma := Measure.dirac true) (pi := piHalf) (S := (∅ : Set Bool)) (M := 2) (phi := 1 / 2)
    (eps := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    MeasurableSet.empty (by simp) ?_ ?_ (ls_const piHalf) ?_
  · -- `dirac true` is `2`-warm with respect to `piHalf`.
    intro A hA
    rw [Set.sdiff_empty, hofReal2]
    by_cases h : true ∈ A
    · have h1 : (1 : ℝ≥0∞) / 2 ≤ piHalf A := by
        rw [← piHalf_singleton true]
        exact measure_mono (Set.singleton_subset_iff.2 h)
      calc Measure.dirac true A ≤ 1 := prob_le_one
        _ = 2 * (1 / 2) := by
            rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        _ ≤ 2 * piHalf A := by gcongr
    · simp [Measure.dirac_apply' _ hA, h]
  · -- the conductance of the uniform resampler is `1/2`.
    rw [conductance_const_piHalf, hhalf]
  · -- `252` is past the deadline: `lsThreshold 2 (1/2) (1/2) = 4·log 64 ≤ 4·63`.
    have hlog : Real.log 64 ≤ 63 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 64 by norm_num)
      linarith
    rw [lsThreshold, show (8 : ℝ) * 2 / (1 / 2) ^ 2 = 64 by norm_num,
      show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]
    rw [div_div_eq_mul_div, div_one]
    push_cast
    linarith

#print axioms tvLe_iterate_const_piHalf

end AxiomCheck

end Arlib.MarkovChains
