/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.HitAndRunMixing
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.BallWalkConductance

/-!
# Discharging `hLS`: Corollary 1.5 of Lovász–Simonovits is a theorem of this repository

`Arlib/MarkovChains/Continuous/HitAndRunMixing.lean` carries the Lovász–Simonovits decay
bound as an inline `∀`-binder `hLS`, and its module docstring (`§ What is assumed`, item
**(A)**) says that the implication *conductance ⟹ geometric decay* "is **not** proved
anywhere in this repository".
**That statement is out of date.**  It is proved, in two files that
`HitAndRunMixing.lean` does not import:

* `Arlib/MarkovChains/Continuous/Cheeger.lean:1584` — `sq_conductance_div_two_le_spectralGap`,
  the hard direction of Cheeger, `Φ²/2 ≤ gap`, for a reversible Markov kernel on a
  probability space with a non-empty admissible family.
* `Arlib/MarkovChains/Continuous/L2Mixing.lean:976` —
  `tvLe_iterate_of_ofReal_le_conductance`, which is *literally the body of the `hLS`
  binder*, for a reversible kernel with `HasNonnegSpectrum` and a non-empty admissible
  family.

This module is therefore **glue, not new mathematics**.  What it adds is the four things
that stand between `L2Mixing.tvLe_iterate_of_ofReal_le_conductance` and an `exact`-discharge
of `HitAndRunMixing.hLS`:

1. `hLS` does not carry `conductance P pi ≠ ⊤`, and `tvLe_iterate_of_ofReal_le_conductance`
   needs it.  `smallSets_nonempty_of_rayleighSet_nonempty` and
   `conductance_ne_top_of_rayleighSet_nonempty` remove that obligation: a chain with a
   non-empty admissible family automatically has finite conductance.
2. The hypothesis `(rayleighSet P pi).Nonempty` mentions the kernel and is awkward for a
   caller.  `rayleighSet_nonempty_of_smallSets_nonempty` replaces it by the **kernel-free**
   `(SmallSets pi (1/2)).Nonempty` — "some measurable set has mass in `(0, 1/2]`" — which is
   the same hypothesis `conductance_le_one` already uses, and which transfers to `lazy P`
   and to any other kernel with the same stationary measure for free.
3. `ls_of_hasNonnegSpectrum` — **the `hLS` binder, verbatim, proved.**
4. `ls_lazy` — the same for `lazy P`, where the spectral hypothesis is not an assumption at
   all: `hasNonnegSpectrum_lazy` (`BallWalkConductance.lean:975`) supplies it from
   reversibility of `P` alone.

## Main results

* `smallSets_nonempty_of_rayleighSet_nonempty` — if some `L²(pi)` function has non-zero
  variance then some measurable set has `pi`-mass in `(0, 1/2]`.  Proved by the median
  (`Cheeger.exists_median`): if every set of mass `≤ 1/2` were null, both `{f > m}` and
  `{f < m}` would be null, so `f` would be a.e. constant.
* `conductance_ne_top_of_rayleighSet_nonempty`, `rayleighSet_nonempty_of_smallSets_nonempty`,
  `rayleighSet_nonempty_iff_smallSets_nonempty` — the resulting dictionary.
* **`ls_of_hasNonnegSpectrum`** — the `hLS` binder of
  `HitAndRunMixing.tvLe_iterate_of_exceptional_of_ls`, discharged for a reversible kernel
  with non-negative spectrum on a space carrying a set of mass in `(0, 1/2]`.
* **`ls_lazy`** — the same for `lazy P`, from `IsReversible P pi` alone.
* **`tvLe_iterate_of_exceptional_of_isReversible`** — Theorem 1.1 of Lovász–Vempala with the
  `hLS` binder *eliminated*.  This is the `exact`-compatibility test of
  `ls_of_hasNonnegSpectrum`: it is proved by handing `ls_of_hasNonnegSpectrum` to
  `tvLe_iterate_of_exceptional_of_ls` at its `hLS` slot, with no massaging.
* **`tvLe_iterate_lazy_of_exceptional`** — Theorem 1.1 for `lazy P` at half the conductance,
  with **no** spectral hypothesis at all beyond reversibility of `P`.
* `ofReal_half_le_conductance_lazy`, `lsThreshold_half` — the exact price of laziness:
  half the conductance, four times the deadline.
* `mixesWithin_of_conductance_of_smallSets` — the same in `MixesWithin` form.
* **`tvLe_iterate_lazy_hitAndRun`** and **`tvLe_iterate_lazy_hitAndRun_unitBall`** — Theorem
  1.1 for `lazy (hitAndRun K)`.  In the second, `hphi` is discharged too, so the only
  residual assumptions are `hLem41` (the paper's Lemma 4.1) and `hIso` (its Theorem 2.1).
* `ls_lazy_const_piHalf`, `tvLe_iterate_const_piHalf_of_isReversible` — the non-vacuity
  witnesses.

## Why a spectral hypothesis is unavoidable, and what shape it takes

`hLS` is **false** for a general reversible chain: `HitAndRunMixing.lean`'s module docstring
(`§ What is assumed`, item **(A)**) records the swap kernel `P x = dirac (!x)` on `Bool`,
which is `piHalf`-reversible with conductance `1`,
`2`-warm from `dirac true`, and has `d_TV = 1/2` for every `t` against a bound `√2·2^{-t}`.
The hypothesis that rules it out is `HasNonnegSpectrum P pi` (`L2Mixing.lean:439`),
`0 ≤ ∫ f · (T f) dpi` — a property of the kernel that names neither a conductance nor a
mixing rate.  Laziness is what buys it in practice: `hasNonnegSpectrum_lazy` proves it for
`lazy P` from reversibility of `P` alone, and `conductance_lazy` says the price is exactly a
factor `2` in the conductance, i.e. a factor `4` in the deadline.

## What is *not* discharged here

* **`hLSs`, the `s`-conductance form of Corollary 1.5** — the `hLSs` binder of
  `HitAndRunMixing.tvLe_iterate_of_sConductance` — is **not** reachable by this route, and
  not for a bookkeeping reason.  Its premise is
  `ofReal ph ≤ conductanceS P pi s`, and `conductance ≤ conductanceS`
  (`HitAndRunMixing.conductance_le_conductanceS`), so an `Φ_s` bound is *strictly weaker*
  than the `Φ` bound Cheeger consumes: a chain whose small sets leak nothing has `Φ = 0` and
  `Φ_s > 0`, and the `L²` route then gives nothing.  Discharging `hLSs` needs the
  Lovász–Simonovits curve/localisation argument itself (plus, by that file's
  `§ A non-vacuity witness for the hLSs binder`, an atomless `pi`).  It remains a binder,
  used only by `tvLe_iterate_of_sConductance`, which nothing downstream of hit-and-run
  calls.
* **`hLS` for the *plain* `hitAndRun K` kernel**, which is the shape
  `HitAndRunMixing.tvLe_iterate_hitAndRun` and `tvLe_iterate_hitAndRun_unitBall` ask for.
  This route discharges `hLS` for `lazy (hitAndRun K)`, at conductance `Φ/2`.  That is not a
  defect of the route: it is exactly the gap identified in `HitAndRunMixing.lean`'s
  `§ Errors and gaps found in the paper`, item 2, in
  *Hit-and-Run from a Corner* ("Corollary 1.5 is applied to a chain with no laziness or
  spectral hypothesis").  Closing it needs a hit-and-run-specific spectral fact — that the
  chain holds at its current point often enough — which nothing in this repository proves.

## Reused rather than rebuilt

* `Arlib.MarkovChains.tvLe_iterate_of_ofReal_le_conductance`, `HasNonnegSpectrum`,
  `hasNonnegSpectrum_const`, `mixesWithin_of_conductance` (`L2Mixing.lean`).
* `Arlib.MarkovChains.rayleighSet`, `AdmissibleL2`, `exists_median`, `varianceReal_indicator`,
  `memLp_two_indicator`, `varianceReal_eq_zero_iff` (`Cheeger.lean`).
* `Arlib.MarkovChains.lazy`, `isReversible_lazy`, `hasNonnegSpectrum_lazy`, `conductance_lazy`
  (`BallWalkConductance.lean`).
* `Arlib.MarkovChains.conductance_le_one`, `SmallSets`, `singleton_mem_smallSets`
  (`Conductance.lean`).
* `Arlib.MarkovChains.tvLe_iterate_of_exceptional_of_ls`, `lsThreshold` (`HitAndRunMixing.lean`).

## References

* Lovász–Simonovits, *Random walks in a convex body and an improved volume algorithm*,
  RSA 1993, Corollary 1.5.
* Lovász–Vempala, *Hit-and-Run from a Corner*, SIAM J. Comput. 35 (2006) 985–1005, §5.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## A non-degenerate space: `SmallSets` versus `rayleighSet`

Two non-degeneracy hypotheses appear in the two halves of the argument and have to be
reconciled.  `Cheeger.lean` and `L2Mixing.lean` ask for `(rayleighSet P pi).Nonempty` —
forced by `sInf ∅ = 0` over `ℝ`.  `Conductance.lean` asks for `(SmallSets pi (1/2)).Nonempty`
— forced by `⨅ over ∅ = ⊤` over `ℝ≥0∞`.  They are equivalent, and the second is the better
hypothesis to expose: it does not mention the kernel. -/

/-- **A chain with an admissible `L²` function lives on a space with a small set.**

If every measurable set of `pi`-mass at most `1/2` were null then, taking a median `m` of a
measurable representative `f'` (`Arlib.MarkovChains.exists_median`), both `{f' > m}` and
`{f' < m}` would be null — so `f'` would be `pi`-a.e. equal to the constant `m` and its
variance would vanish, contradicting admissibility.

This is what removes the hypothesis `conductance P pi ≠ ⊤` from
`Arlib.MarkovChains.tvLe_iterate_of_ofReal_le_conductance`, which the `hLS` binder of
`HitAndRunMixing.lean` does not supply. -/
theorem smallSets_nonempty_of_rayleighSet_nonempty {P : Kernel Ω Ω} {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hne : (rayleighSet P pi).Nonempty) :
    (SmallSets pi (1 / 2)).Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hnull : ∀ S : Set Ω, MeasurableSet S → pi S ≤ 1 / 2 → pi S = 0 := by
    intro S hS hle
    by_contra h0
    have hmem : S ∈ SmallSets pi (1 / 2) := ⟨hS, pos_iff_ne_zero.2 h0, hle⟩
    rw [hemp] at hmem
    exact hmem
  obtain ⟨r, f, ⟨hmem, hv⟩, rfl⟩ := hne
  set f' : Ω → ℝ := hmem.aestronglyMeasurable.mk f with hf'def
  have hff' : f =ᵐ[pi] f' := hmem.aestronglyMeasurable.ae_eq_mk
  have hf'meas : Measurable f' := hmem.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hf'mem : MemLp f' 2 pi := MemLp.ae_eq hff' hmem
  have hf'v : varianceReal pi f' ≠ 0 := by
    rwa [varianceReal, ← ProbabilityTheory.variance_congr hff']
  obtain ⟨m, hm1, hm2⟩ := exists_median (pi := pi) hf'meas
  have h1 : pi {x | m < f' x} = 0 :=
    hnull _ (measurableSet_lt measurable_const hf'meas) hm1
  have h2 : pi {x | f' x < m} = 0 :=
    hnull _ (measurableSet_lt hf'meas measurable_const) hm2
  have hconst : f' =ᵐ[pi] fun _ => m := by
    have hsub : {x : Ω | ¬ f' x = m} ⊆ {x | m < f' x} ∪ {x | f' x < m} := by
      intro x hx
      rcases lt_trichotomy (f' x) m with h | h | h
      · exact Or.inr h
      · exact absurd h hx
      · exact Or.inl h
    have : pi {x : Ω | ¬ f' x = m} = 0 :=
      measure_mono_null hsub (measure_union_null h1 h2)
    exact this
  refine hf'v ?_
  rw [varianceReal, ProbabilityTheory.variance_congr hconst]
  exact varianceReal_const pi m

/-- **A chain with an admissible `L²` function has finite conductance.**  Immediate from
`smallSets_nonempty_of_rayleighSet_nonempty` and `conductance_le_one`. -/
theorem conductance_ne_top_of_rayleighSet_nonempty {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hne : (rayleighSet P pi).Nonempty) :
    conductance P pi ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (conductance_le_one P pi (smallSets_nonempty_of_rayleighSet_nonempty hne))

/-- **The converse**: a measurable set of mass in `(0, 1/2]` gives an admissible function,
namely its indicator, whose variance is `p(1 − p) ≥ p/2 > 0`.

The point of this direction is that `(SmallSets pi (1/2)).Nonempty` mentions only `pi`, so a
caller can discharge it once and use it for `P`, for `lazy P`, and for any other kernel with
the same stationary measure. -/
theorem rayleighSet_nonempty_of_smallSets_nonempty (P : Kernel Ω Ω) {pi : Measure Ω}
    [IsProbabilityMeasure pi] (h : (SmallSets pi (1 / 2)).Nonempty) :
    (rayleighSet P pi).Nonempty := by
  obtain ⟨S, hSm, hSpos, hShalf⟩ := h
  exact rayleighSet_nonempty_of_smallSet P hSm hSpos hShalf

/-- The two non-degeneracy hypotheses are the same one. -/
theorem rayleighSet_nonempty_iff_smallSets_nonempty (P : Kernel Ω Ω) [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] :
    (rayleighSet P pi).Nonempty ↔ (SmallSets pi (1 / 2)).Nonempty :=
  ⟨smallSets_nonempty_of_rayleighSet_nonempty,
    rayleighSet_nonempty_of_smallSets_nonempty P⟩

/-! ## The `hLS` binder, proved

The statement below is copied **verbatim** from the `hLS` hypothesis of
`Arlib.MarkovChains.tvLe_iterate_of_exceptional_of_ls`
(the `hLS` hypothesis of `tvLe_iterate_of_exceptional_of_ls`), so that it discharges that
binder by `exact`.  The proof is
one application of `Arlib.MarkovChains.tvLe_iterate_of_ofReal_le_conductance`
(`L2Mixing.lean:976`), whose own ingredients are Cheeger's inequality
(`Cheeger.sq_conductance_div_two_le_spectralGap`), the `L²` contraction
(`L2Mixing.varianceReal_markovIter_le`) and the `χ²`→TV comparison
(`L2Mixing.tvLe_withDensity`).

The binder's own hypothesis `ph ≤ 1` is not needed and is ignored.  What *is* needed and the
binder does not supply — `conductance P pi ≠ ⊤` — comes from `hsmall`. -/

/-- **Corollary 1.5 of Lovász–Simonovits, in the exact shape of the `hLS` binder.**

For a reversible Markov kernel with non-negative spectrum, on a probability space carrying at
least one measurable set of mass in `(0, 1/2]`:

    d_TV(mu P^t, pi)  ≤  √W · (1 − ph²/2)^t     for every `W`-warm `mu`,

whenever `ph ≤ Φ(P)`.

**The spectral hypothesis is not removable.**  Without it the statement is false: the swap
kernel `P x = dirac (!x)` on `Bool` is `piHalf`-reversible with `Φ = 1`, `dirac true` is
`2`-warm, and `d_TV = 1/2` for every `t` while the bound `√2·2^{-t}` tends to `0`
(`HitAndRunMixing.lean`, `§ What is assumed`, item **(A)**).  `HasNonnegSpectrum` is what
excludes it; `ls_lazy` below
derives it from laziness. -/
theorem ls_of_hasNonnegSpectrum {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    (hsmall : (SmallSets pi (1 / 2)).Nonempty) :
    ∀ ph W : ℝ, 0 < ph → ph ≤ 1 → 1 ≤ W → ENNReal.ofReal ph ≤ conductance P pi →
      ∀ mu : Measure Ω, IsProbabilityMeasure mu → Arlib.IsWarm (ENNReal.ofReal W) mu pi →
        ∀ t : ℕ, Arlib.TVLe (iterate P mu t) pi
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t)) := by
  have hne : (rayleighSet P pi).Nonempty := rayleighSet_nonempty_of_smallSets_nonempty P hsmall
  have hc : conductance P pi ≠ ⊤ := conductance_ne_top_of_rayleighSet_nonempty hne
  intro ph W hph0 _ hW hcond mu hmu hwarm t
  haveI := hmu
  exact tvLe_iterate_of_ofReal_le_conductance hrev hpsd hne hW hwarm hph0 hc hcond t

/-- **The `hLS` binder for a lazy chain**, with *no* spectral hypothesis: laziness supplies
it (`Arlib.MarkovChains.hasNonnegSpectrum_lazy`, `BallWalkConductance.lean:975`).

`Arlib.MarkovChains.conductance_lazy` says the price is exactly a factor `2` in the
conductance — hence a factor `4` in the mixing deadline (`lsThreshold_half`). -/
theorem ls_lazy {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω} [IsProbabilityMeasure pi]
    (hrev : IsReversible P pi) (hsmall : (SmallSets pi (1 / 2)).Nonempty) :
    ∀ ph W : ℝ, 0 < ph → ph ≤ 1 → 1 ≤ W → ENNReal.ofReal ph ≤ conductance (lazy P) pi →
      ∀ mu : Measure Ω, IsProbabilityMeasure mu → Arlib.IsWarm (ENNReal.ofReal W) mu pi →
        ∀ t : ℕ, Arlib.TVLe (iterate (lazy P) mu t) pi
          (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t)) :=
  ls_of_hasNonnegSpectrum (isReversible_lazy hrev) (hasNonnegSpectrum_lazy hrev) hsmall

/-- **Half a conductance bound for `P` is a conductance bound for `lazy P`** — exactly, by
`Arlib.MarkovChains.conductance_lazy`. -/
theorem ofReal_half_le_conductance_lazy {P : Kernel Ω Ω} {pi : Measure Ω} {phi : ℝ}
    (hcond : ENNReal.ofReal phi ≤ conductance P pi) :
    ENNReal.ofReal (phi / 2) ≤ conductance (lazy P) pi := by
  rw [conductance_lazy, ENNReal.ofReal_div_of_pos (by norm_num),
    show ENNReal.ofReal (2 : ℝ) = 2 by simp]
  gcongr

/-- **Laziness costs a factor `4` in the deadline**: `lsThreshold M (φ/2) ε = 4 · lsThreshold
M φ ε`.  Stated with no positivity hypothesis — at `φ = 0` both sides are `0` by the
`x / 0 = 0` convention. -/
theorem lsThreshold_half (M phi eps : ℝ) :
    lsThreshold M (phi / 2) eps = 4 * lsThreshold M phi eps := by
  rw [lsThreshold, lsThreshold, div_pow, div_div_eq_mul_div]
  ring

/-! ## Theorem 1.1 of Lovász–Vempala, with the `hLS` binder eliminated

The two theorems below are the point of this file.  Each is proved by handing
`ls_of_hasNonnegSpectrum` (resp. `ls_lazy`) to
`Arlib.MarkovChains.tvLe_iterate_of_exceptional_of_ls` at its `hLS` slot — literally by
`exact`, with no massaging.  That composition *is* the compatibility check. -/

/-- **Theorem 1.1, unconditionally on `hLS`.**  A reversible Markov chain with non-negative
spectrum, conductance at least `phi`, on a space with a set of mass in `(0, 1/2]`, started
from a law dominated by `M·pi` off an exceptional set of mass `ε/2`, is within total
variation `ε` of `pi` after `log(8M/ε²)/phi²` steps.

Compare `Arlib.MarkovChains.tvLe_iterate_of_exceptional_of_ls`, which is this statement with
`hrev`, `hpsd`, `hsmall` replaced by the binder `hLS`. -/
theorem tvLe_iterate_of_exceptional_of_isReversible {P : Kernel Ω Ω} [IsMarkovKernel P]
    {sigma pi : Measure Ω} [IsProbabilityMeasure sigma] [IsProbabilityMeasure pi] {S : Set Ω}
    {M phi eps : ℝ} (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    (hM : 1 ≤ M) (hphi0 : 0 < phi) (hphi1 : phi ≤ 1) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hSm : MeasurableSet S) (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set Ω, MeasurableSet A → sigma (A \ S) ≤ ENNReal.ofReal M * pi A)
    (hcond : ENNReal.ofReal phi ≤ conductance P pi)
    {m : ℕ} (hm : lsThreshold M phi eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate P sigma m) pi (ENNReal.ofReal eps) :=
  tvLe_iterate_of_exceptional_of_ls hM hphi0 hphi1 heps0 heps1 hSm hS hdom hcond
    (ls_of_hasNonnegSpectrum hrev hpsd hsmall) hm

/-- **Theorem 1.1 for the lazy version of any reversible chain**, with no spectral hypothesis
whatsoever.  The conductance hypothesis is on the *plain* chain `P`; the deadline is
`4·log(8M/ε²)/phi²`, four times that of `tvLe_iterate_of_exceptional_of_isReversible`, which
is exactly the price `conductance_lazy` charges. -/
theorem tvLe_iterate_lazy_of_exceptional {P : Kernel Ω Ω} [IsMarkovKernel P]
    {sigma pi : Measure Ω} [IsProbabilityMeasure sigma] [IsProbabilityMeasure pi] {S : Set Ω}
    {M phi eps : ℝ} (hrev : IsReversible P pi) (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    (hM : 1 ≤ M) (hphi0 : 0 < phi) (hphi1 : phi ≤ 1) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hSm : MeasurableSet S) (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set Ω, MeasurableSet A → sigma (A \ S) ≤ ENNReal.ofReal M * pi A)
    (hcond : ENNReal.ofReal phi ≤ conductance P pi)
    {m : ℕ} (hm : 4 * lsThreshold M phi eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy P) sigma m) pi (ENNReal.ofReal eps) := by
  refine tvLe_iterate_of_exceptional_of_isReversible (isReversible_lazy hrev)
    (hasNonnegSpectrum_lazy hrev) hsmall hM (by linarith) (by linarith) heps0 heps1 hSm hS hdom
    (ofReal_half_le_conductance_lazy hcond) ?_
  rw [lsThreshold_half]
  exact hm

/-- **The `MixesWithin` form**, with the kernel-free non-degeneracy hypothesis.  Same content
as `Arlib.MarkovChains.mixesWithin_of_conductance` (`L2Mixing.lean:963`); only `hne` is
traded for `hsmall`. -/
theorem mixesWithin_of_conductance_of_smallSets {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi) (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M phi eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0 pi) (hphi0 : 0 < phi) (hphi1 : phi ≤ 1)
    (heps : 0 < eps) (hphi : phi ≤ (conductance P pi).toReal) {t : ℕ}
    (ht : conductanceMixingTime M phi eps ≤ t) :
    MixesWithin P pi mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_of_conductance hrev hpsd (rayleighSet_nonempty_of_smallSets_nonempty P hsmall)
    hM hwarm hphi0 hphi1 heps hphi ht

/-! ## The hit-and-run instance

`Arlib.MarkovChains.tvLe_iterate_hitAndRun` states Theorem 1.1 for the *plain* kernel
`hitAndRun K` and leaves `hLS` as a binder.  This route cannot discharge that binder: the
plain hit-and-run walk is not known here to have non-negative spectrum, and
`HitAndRunMixing.lean`'s `§ Errors and gaps found in the paper`, item 2, records that the
paper's own §5 applies Corollary 1.5 to it
with no laziness or spectral hypothesis — a genuine gap in *Hit-and-Run from a Corner*, not a
bookkeeping loss.

What *is* dischargeable is the same statement for `lazy (hitAndRun K)`, with **every**
hypothesis of `tvLe_iterate_of_exceptional_of_ls` proved rather than assumed, at a deadline
four times as long.  The conductance hypothesis is unchanged — it is still the paper's
Theorem 4.2 for the plain walk. -/

/-- **Theorem 1.1 for the lazy hit-and-run walk, with `hLS` discharged.**

Reversibility comes from `Arlib.MarkovChains.isReversible_hitAndRun`, the spectral hypothesis
from `Arlib.MarkovChains.hasNonnegSpectrum_lazy`, and the non-degeneracy from
`Arlib.MarkovChains.exists_smallSet_uniformOn`; so the only hypothesis left carrying
mathematical content is `hphi`, the conductance bound (the paper's Theorem 4.2), exactly as
in `Arlib.MarkovChains.tvLe_iterate_hitAndRun`.

The deadline is `4 · lvThreshold n r R M eps = 2⁵⁸ · n² · (R²/r²) · log(8M/ε²)`; the factor
`4` is `conductance_lazy` — laziness halves the conductance, exactly. -/
theorem tvLe_iterate_lazy_hitAndRun {n : ℕ} (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKm : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {sigma : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure sigma]
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    {M eps : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hS : sigma S ≤ ENNReal.ofReal (eps / 2))
    (hdom : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      sigma (A \ S) ≤ ENNReal.ofReal M * Arlib.uniformOn volume K A)
    (hphi : ENNReal.ofReal (r / (2 ^ 28 * (n : ℝ) * R))
      ≤ conductance (hitAndRun K) (Arlib.uniformOn volume K))
    {m : ℕ} (hm : 4 * lvThreshold n r R M eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (hitAndRun K)) sigma m) (Arlib.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hphi0 : 0 < r / (2 ^ 28 * (n : ℝ) * R) := by positivity
  have hphi1 : r / (2 ^ 28 * (n : ℝ) * R) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ := exists_smallSet_uniformOn hn hKm hK0 hKtop
  refine tvLe_iterate_lazy_of_exceptional (isReversible_hitAndRun hKm)
    ⟨S0, hS0m, hS0pos, hS0half⟩ hM hphi0 hphi1 heps0 heps1 hSm hS hdom hphi ?_
  rw [lsThreshold_eq_lvThreshold hn hr hR]
  exact hm

/-- **Theorem 1.1 for the lazy hit-and-run walk on a body with a unit inball**, with both
`hphi` *and* `hLS` discharged.

This is the exact analogue of `Arlib.MarkovChains.tvLe_iterate_hitAndRun_unitBall`
for the lazy kernel, and it is the closest this development
comes to an unconditional Theorem 1.1: the **only** residual assumptions are `hLem41` (the
paper's Lemma 4.1) and `hIso` (the paper's Theorem 2.1, the weighted isoperimetric
inequality), both inherited verbatim from `conductance_hitAndRun_ge`.  The
Lovász–Simonovits binder `hLS` is gone.

`volume K ≠ 0` and `volume K ≠ ⊤` are *derived* here from the inball and the circumball, so
they are not extra hypotheses. -/
theorem tvLe_iterate_lazy_hitAndRun_unitBall {n : ℕ} (hn : 1 ≤ n)
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
    {m : ℕ} (hm : 4 * lvThreshold n 1 R M eps ≤ (m : ℝ)) :
    Arlib.TVLe (iterate (lazy (hitAndRun K)) sigma m) (Arlib.uniformOn volume K)
      (ENNReal.ofReal eps) := by
  have hR : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hK0 : volume K ≠ 0 := by
    have hpos : 0 < volume (Metric.closedBall z 1) :=
      Metric.measure_closedBall_pos volume z one_pos
    exact (lt_of_lt_of_le hpos (measure_mono hball)).ne'
  have hKtop : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hout)
  have hphi := ofReal_inv_le_conductance_hitAndRun_of_unitBall hn hKc hKcl hKm hball hR hout
    hLem41 hIso
  refine tvLe_iterate_lazy_hitAndRun hn hKm hK0 hKtop one_pos hR hR1 hM heps0 heps1 hSm hS
    hdom ?_ hm
  simpa using hphi

/-! ## Non-vacuity (`CLAUDE.md` §11)

Every theorem above quantifies over a hypothesis bundle, so each bundle needs a witness.
`ls_of_hasNonnegSpectrum`'s bundle is `(hrev, hpsd, hsmall)`; `ls_lazy`'s is `(hrev, hsmall)`.
Both are exhibited on the two-point space, and in each case the *conclusion* is non-trivial:
the conductance is `1/2` (resp. `1/4`), not `0`, so the bound is a real decay rate. -/

/-- **The lazy uniform resampler on `Bool` satisfies the `hLS` binder**, and its conductance
is `1/4` — non-zero, so the decay bound is non-trivial.  Nothing but reversibility of the
underlying kernel is assumed: the spectral hypothesis is supplied by laziness. -/
theorem ls_lazy_const_piHalf :
    (∀ ph W : ℝ, 0 < ph → ph ≤ 1 → 1 ≤ W →
        ENNReal.ofReal ph ≤ conductance (lazy (Kernel.const Bool piHalf)) piHalf →
        ∀ mu : Measure Bool, IsProbabilityMeasure mu →
          Arlib.IsWarm (ENNReal.ofReal W) mu piHalf →
          ∀ t : ℕ, Arlib.TVLe (iterate (lazy (Kernel.const Bool piHalf)) mu t) piHalf
            (ENNReal.ofReal (Real.sqrt W * (1 - ph ^ 2 / 2) ^ t)))
      ∧ conductance (lazy (Kernel.const Bool piHalf)) piHalf = 1 / 4 := by
  refine ⟨ls_lazy (isReversible_const piHalf) ⟨{true}, singleton_mem_smallSets true⟩, ?_⟩
  rw [conductance_lazy, conductance_const_piHalf, div_eq_mul_inv, div_eq_mul_inv,
    div_eq_mul_inv, one_mul, one_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num)]

/-- **Non-vacuity witness for `tvLe_iterate_of_exceptional_of_isReversible`.**  Every one of
its hypotheses is satisfiable at once, with a non-trivial conclusion (`ε = 1/2 < 1`), and the
conclusion is derived *through* that theorem.

This is `Arlib.MarkovChains.tvLe_iterate_const_piHalf` with the
`hLS` binder no longer supplied by hand: `ls_const` is replaced by the *proved* hypotheses
`isReversible_const` and `hasNonnegSpectrum_const`. -/
theorem tvLe_iterate_const_piHalf_of_isReversible :
    Arlib.TVLe (iterate (Kernel.const Bool piHalf) (Measure.dirac true) 252) piHalf
      (ENNReal.ofReal (1 / 2)) := by
  have hofReal2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  refine tvLe_iterate_of_exceptional_of_isReversible (P := Kernel.const Bool piHalf)
    (sigma := Measure.dirac true) (pi := piHalf) (S := (∅ : Set Bool)) (M := 2) (phi := 1 / 2)
    (eps := 1 / 2) (isReversible_const piHalf) (hasNonnegSpectrum_const piHalf)
    ⟨{true}, singleton_mem_smallSets true⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    MeasurableSet.empty (by simp) ?_ ?_ ?_
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
    rw [conductance_const_piHalf, ofReal_one_half]
  · -- `252` is past the deadline: `lsThreshold 2 (1/2) (1/2) = 4·log 64 ≤ 4·63`.
    have hlog : Real.log 64 ≤ 63 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 64 by norm_num)
      linarith
    rw [lsThreshold, show (8 : ℝ) * 2 / (1 / 2) ^ 2 = 64 by norm_num,
      show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]
    rw [div_div_eq_mul_div, div_one]
    push_cast
    linarith

/-! ### Axiom audit (`CLAUDE.md` §4)

Every declaration of this file, plus the two upstream results it rests on — the hard
direction of Cheeger and the `L²` mixing bound — must report exactly
`[propext, Classical.choice, Quot.sound]`.  The upstream two are listed here deliberately:
this file's headline claim is that they *exist and are clean*, so it checks them rather than
taking their own files' word for it. -/

section AxiomCheck

#print axioms sq_conductance_div_two_le_spectralGap
#print axioms tvLe_iterate_of_ofReal_le_conductance
#print axioms hasNonnegSpectrum_lazy

#print axioms smallSets_nonempty_of_rayleighSet_nonempty
#print axioms conductance_ne_top_of_rayleighSet_nonempty
#print axioms rayleighSet_nonempty_of_smallSets_nonempty
#print axioms rayleighSet_nonempty_iff_smallSets_nonempty
#print axioms ls_of_hasNonnegSpectrum
#print axioms ls_lazy
#print axioms ofReal_half_le_conductance_lazy
#print axioms lsThreshold_half
#print axioms tvLe_iterate_of_exceptional_of_isReversible
#print axioms tvLe_iterate_lazy_of_exceptional
#print axioms mixesWithin_of_conductance_of_smallSets
#print axioms tvLe_iterate_lazy_hitAndRun
#print axioms tvLe_iterate_lazy_hitAndRun_unitBall
#print axioms ls_lazy_const_piHalf
#print axioms tvLe_iterate_const_piHalf_of_isReversible

end AxiomCheck

end Arlib.MarkovChains
