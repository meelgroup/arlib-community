/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.TrajTransfer
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.Warmness

/-!
# Wasted steps: the speedy-walk step count converted to a ball-walk step count

This file formalises Cousins–Vempala's `lem:speedy-to-ball` (`1409.6011/vol3_journal.tex:915`,
proof at `:919`–`:937`):

> If the average local conductance is at least `λ`, `M(Q₀, Q) ≤ M`, and the speedy walk takes
> `t` steps, then the expected number of steps of the corresponding ball walk is at most
> `M·t/λ`.

The speedy walk is the sub-chain of *proper* ball-walk steps — those whose proposal lands in
`K`.  Its stationary law is `ellProb K δ`, the law with density proportional to the local
conductance `ell K δ`, while the ball walk's is uniform.  A speedy step is therefore not free:
from `x` the ball walk must be run for a `Geom(ell K δ x)` number of steps before one proper
step happens, and the steps in between are *wasted*.  This file bounds the total.

## The two ingredients, and where each comes from

Cousins–Vempala's proof has exactly two ingredients, and **both already existed in this
repository**; the new content here is their combination.

1. **Warmth is preserved along the chain** — CV's `Qᵢ(S) ≤ M·Q(S)` by induction on `i`.
   This is `Arlib.MarkovChains.isWarm_iterate` (`Warmness.lean`), proved for an arbitrary
   kernel with an arbitrary stationary law.  What is new here is its *integral* consequence,
   `lintegral_le_of_isWarm`: a warm law overestimates any `ℝ≥0∞` observable by at most the
   factor `M`, with no measurability or integrability hypothesis.
2. **From `x`, the expected number of ball-walk steps until a proper step is `1/ℓ(x)`.**
   This is `Arlib.MarkovChains.lintegral_exitTime_pathMeasure_ballWalk` (`TrajTransfer.lean`),
   which computes the mean of the exit time `inf {i | ωᵢ ≠ x}` of the *actual* ball-walk
   trajectory started at `x` to be exactly `(ell K δ x)⁻¹`.  The count is the
   trials-including-the-successful-one convention of `Arlib/Probability/Geometric.lean`
   (`integral_geometricMeasure_trials`), which is why the mean is `1/ℓ` and not `(1-ℓ)/ℓ`.
   What is new here is the averaged form `lintegral_lintegral_exitTime_pathMeasure_ballWalk`,
   which lets that mean be integrated against the law of the current speedy state.

The remaining equality of CV's display — `∫_K (1/ℓ) dQ = 1/λ`, "because reweighting `Q ∝ ℓ·f`
by `1/ℓ` gives the ball walk's law `∝ f`" — is `Arlib.MarkovChains.ellMeasure_withDensity_inv_ell`
(`HoldingTime.lean`), for the uniform density `f ≡ 1` this repository's ball walk uses.

## Main results

**The warm-start integral bound** (generic: any measurable space, any kernel).

* `Arlib.MarkovChains.lintegral_le_of_isWarm` — `IsWarm M μ pi` gives
  `∫⁻ f ∂μ ≤ M * ∫⁻ f ∂pi` for every `f : Ω → ℝ≥0∞`.
* `Arlib.MarkovChains.lintegral_iterate_le_of_isWarm` — the same bound at every time `i`
  along the chain, by `isWarm_iterate`.
* `Arlib.MarkovChains.sum_lintegral_iterate_le_of_isWarm` — summed over `t` steps:
  `∑_{i<t} ∫⁻ f ∂(iterate P μ i) ≤ t * (M * ∫⁻ f ∂pi)`.  This is CV's "by linearity of
  expectation" step, isolated from anything about walks.

**The cost of one speedy step.**

* `Arlib.MarkovChains.lintegral_inv_ell_ellProb` — `∫⁻ (ell)⁻¹ dellProb = (∫_K ell)⁻¹ · vol K`,
  i.e. `1/λ`.
* `Arlib.MarkovChains.mul_lintegral_inv_ell_ellProb_le_one_of_le_avg` — under
  `λ ≤ avgLocalConductance K δ`, `λ · ∫⁻ (ell)⁻¹ dellProb ≤ 1`.  Stated multiplicatively so no
  `ℝ≥0∞` division appears and so it says the right thing at `λ = 0`.

**`lem:speedy-to-ball`.**

* `Arlib.MarkovChains.mul_sum_lintegral_inv_ell_iterate_speedyWalk_le` — the core form,
  `NeZero`-free:

      λ · ∑_{i<t} ∫⁻ (ell K δ)⁻¹ d(iterate (speedyWalk K δ) Q₀ i)  ≤  t · M.

* `Arlib.MarkovChains.mul_sum_lintegral_exitTime_iterate_speedyWalk_le` — **the headline**,
  the same bound with the integrand replaced by the *proved* mean exit time of the real
  ball-walk trajectory from `x`, so that the left-hand side is a sum of genuine expected
  ball-walk step counts rather than a formal reciprocal.  Costs `[NeZero n]`, inherited from
  `TrajTransfer.lean`.
* `Arlib.MarkovChains.sum_lintegral_inv_ell_iterate_speedyWalk_le` — the divided form
  `∑ ≤ t·M/λ`, under the extra guards `λ ≠ 0`, `λ ≠ ⊤` that `ℝ≥0∞` division needs.

**Non-vacuity.**

* `Arlib.MarkovChains.exists_wastedSteps_witness` — for the unit ball, any `δ > 0` and any
  `t ≥ 1`, every hypothesis above is satisfied simultaneously with `λ` **non-zero and finite**
  and `M = 1`, the left-hand side is **strictly positive and finite**, and the bound holds
  **with equality** (`λ · ∑ = t · M`).  So none of the hypotheses is unsatisfiable and the
  conclusion is sharp — it is attained by the chain started at stationarity.

## What is assumed and not proved

* **`hlam : lam ≤ avgLocalConductance K δ` is a hypothesis, deliberately.**  It is CV's
  `lem:lambda-bound` (`vol3_journal.tex:855`, `λ(f) ≥ 1 − 32·δ^{1/2}n^{1/4}/a^{1/2}` for an
  `a`-rounded logconcave `f`), whose proof goes through Lovász–Vempala's smoothing lemma.
  **Nothing in this repository proves it** and nothing here attempts to.  Every theorem below
  carries it as an explicit binder.
* **`hwarm : IsWarm M Q₀ (ellProb K δ)` is a hypothesis**, exactly as CV's `M(Q₀,Q) ≤ M` is.
  It is checked once, at time zero; `isWarm_iterate` is what makes that enough.

## What is *not* claimed

Read this before quoting the capstone.

1. **The left-hand side is a sum of per-step conditional expectations, not a proved functional
   of a single ball-walk trajectory.**  `∑_{i<t} ∫⁻ (mean holding time) dQᵢ` is precisely the
   quantity CV bound by linearity of expectation, and each summand is a proved expected exit
   time of the real ball walk (`mul_sum_lintegral_exitTime_iterate_speedyWalk_le`).  But the
   identification of that sum with "the number of ball-walk steps the trajectory actually
   takes to realise `t` speedy steps" needs the path-level time change `ω_t = Y_{N t}` —
   extracting the jump chain and the counting process from a path — which is
   `TrajTransfer.lean`'s "What is not proved", item 1, and is **still unproved**.  Do not
   restate the capstone as a statement about a single trajectory.
2. **This is a step-count statement and nothing else.**  There is no complexity field, no cost
   model and no running-time claim anywhere in this repository, and none is introduced here.
   In particular nothing below says anything about the running time of a volume algorithm.
3. **No bound on `λ` and no bound on `M` is proved here** — see "What is assumed" above.
4. **`t` is the number of *speedy* steps, supplied by the caller.**  Nothing here says how
   large `t` must be for the speedy walk to mix; that is a conductance statement and lives
   elsewhere.

## Audit surface

`CLAUDE.md` §11 asks for the audit surface to be findable in minutes.  Since this file is the
only file being added, it is recorded here rather than in `AUDIT.md`:

* **Capstone**: `mul_sum_lintegral_exitTime_iterate_speedyWalk_le` (trajectory form) and
  `mul_sum_lintegral_inv_ell_iterate_speedyWalk_le` (core form).  Read the types only.
* **Hypotheses carried unproved**: `hlam` and `hwarm`, listed above with their CV provenance.
  Every other binder (`hK`, `hδ`, `hK0`, `hKtop`) is a measurability/non-degeneracy guard,
  each discharged for the unit ball inside `exists_wastedSteps_witness`.
* **Non-vacuity**: `exists_wastedSteps_witness`, which also proves the bound is attained.
* **Semantic `def`s**: none.  This file introduces no `def`, no `structure` and no named
  `Prop`; every hypothesis is an inline binder of the theorem that consumes it.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. A warm start overestimates every observable by at most `M`

CV's ingredient (i), in the form the proof consumes it.  `isWarm_iterate` (`Warmness.lean`)
already gives `Qᵢ(S) ≤ M·Q(S)` for every measurable `S` and every `i`; what the cost
computation needs is the same statement for an *integral* rather than for a set, and then
summed over the `t` steps.

Everything in this section is generic: an arbitrary measurable space, an arbitrary kernel,
an arbitrary `ℝ≥0∞`-valued observable.  No measurability of the observable is needed, and
neither side need be finite. -/

section Generic

variable {Om : Type*} [MeasurableSpace Om]

/-- **A warm start overestimates every observable by at most the warmness factor.**  If `μ`
is `M`-warm with respect to `pi` then for every `f : Om → ℝ≥0∞`

    ∫⁻ f ∂μ ≤ M * ∫⁻ f ∂pi.

Assumes nothing beyond `IsWarm M μ pi`: no measurability of `f`, no finiteness, no
probability-measure hypothesis.  Warmness is exactly the domination `μ ≤ M • pi`
(`isWarm_iff_le_smul`), and a lower integral is monotone in its measure. -/
theorem lintegral_le_of_isWarm {M : ℝ≥0∞} {μ pi : Measure Om} (h : IsWarm M μ pi)
    (f : Om → ℝ≥0∞) : ∫⁻ x, f x ∂μ ≤ M * ∫⁻ x, f x ∂pi := by
  have hle : μ ≤ M • pi := (isWarm_iff_le_smul _ _).1 h
  calc ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂(M • pi) := lintegral_mono' hle le_rfl
    _ = M * ∫⁻ x, f x ∂pi := by rw [lintegral_smul_measure, smul_eq_mul]

/-- **The same bound at every time along the chain.**  If the *initial* law is `M`-warm with
respect to a stationary `pi`, then the law at time `i` overestimates every observable by at
most `M`, for every `i`.

This is CV's induction `Qᵢ(S) ≤ M·Q(S)` (`vol3_journal.tex:925`) in integral form; the
induction itself is `isWarm_iterate`, and only the warmness parameter checked at time zero
enters. -/
theorem lintegral_iterate_le_of_isWarm {M : ℝ≥0∞} {μ pi : Measure Om} {P : Kernel Om Om}
    (h : IsWarm M μ pi) (hpi : step P pi = pi) (f : Om → ℝ≥0∞) (i : ℕ) :
    ∫⁻ x, f x ∂(iterate P μ i) ≤ M * ∫⁻ x, f x ∂pi :=
  lintegral_le_of_isWarm (isWarm_iterate h hpi i) f

/-- **CV's linearity-of-expectation step**, isolated from anything about walks: the total
cost of `t` steps of a chain started from an `M`-warm law is at most `t` times the stationary
cost, inflated by `M`:

    ∑_{i<t} ∫⁻ f ∂(iterate P μ i) ≤ t * (M * ∫⁻ f ∂pi).

Assumes `IsWarm M μ pi` and that `pi` is stationary for `P`; nothing about `f`. -/
theorem sum_lintegral_iterate_le_of_isWarm {M : ℝ≥0∞} {μ pi : Measure Om} {P : Kernel Om Om}
    (h : IsWarm M μ pi) (hpi : step P pi = pi) (f : Om → ℝ≥0∞) (t : ℕ) :
    ∑ i ∈ Finset.range t, ∫⁻ x, f x ∂(iterate P μ i) ≤ (t : ℝ≥0∞) * (M * ∫⁻ x, f x ∂pi) := by
  calc ∑ i ∈ Finset.range t, ∫⁻ x, f x ∂(iterate P μ i)
      ≤ ∑ _i ∈ Finset.range t, M * ∫⁻ x, f x ∂pi :=
        Finset.sum_le_sum fun i _ => lintegral_iterate_le_of_isWarm h hpi f i
    _ = (t : ℝ≥0∞) * (M * ∫⁻ x, f x ∂pi) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Generic

/-! ## 2. The cost of one speedy step in stationarity is `1/λ`

CV's display at `vol3_journal.tex:933`:

    ∫_K (1/ℓ) dQ = ∫_K (1/λ) dQ̂ = 1/λ,

"where `Q̂` is the corresponding distribution for the ball walk".  For the uniform density
this repository's ball walk carries, `Q = ellProb K δ` and `Q̂ = uniformOn volume K`, and the
reweighting identity behind the first equality is `ellMeasure_withDensity_inv_ell`
(`HoldingTime.lean`), which is *exact*. -/

/-- **The mean holding time in stationarity**:

    ∫⁻ (ell K δ)⁻¹ dellProb = (∫_K ell)⁻¹ · vol K,

which is `1/λ` for `λ = avgLocalConductance K δ = (∫_K ell)/vol K`.

Assumes `MeasurableSet K` and `δ > 0`; `δ > 0` is what makes the stuck points Lebesgue-null
(`volume_inter_stuckPoints_eq_zero`), without which the reweighting would lose mass. -/
theorem lintegral_inv_ell_ellProb {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ x, (ell K δ x)⁻¹ ∂(ellProb K δ) = (ellMeasure K δ Set.univ)⁻¹ * volume K := by
  rw [ellProb, lintegral_smul_measure, smul_eq_mul, lintegral_inv_ell_ellMeasure hK hδ]

/-- **The average-local-conductance hypothesis in multiplicative form.**  `avgLocalConductance`
is an `ℝ≥0∞` quotient, so a bound on it is only usable once the denominator is known to be
positive and finite; this converts `λ ≤ (∫_K ell)/vol K` into `λ · vol K ≤ ∫_K ell`.

Assumes `vol K ≠ 0` and `vol K ≠ ⊤`. -/
theorem mul_volume_le_ellMeasure_univ_of_le_avg {K : Set (EuclideanSpace ℝ (Fin n))} {δ : ℝ}
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {lam : ℝ≥0∞}
    (hlam : lam ≤ avgLocalConductance K δ) : lam * volume K ≤ ellMeasure K δ Set.univ := by
  rw [ellMeasure_univ]
  rw [avgLocalConductance] at hlam
  exact (ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKtop)).1 hlam

/-- **One speedy step costs at most `1/λ` ball-walk steps, in stationarity.**  Under
`λ ≤ avgLocalConductance K δ`,

    λ · ∫⁻ (ell K δ)⁻¹ dellProb ≤ 1.

Assumes `MeasurableSet K`, `δ > 0`, `vol K ≠ 0`, `vol K ≠ ⊤` and the `λ`-bound.  Stated
multiplicatively so that it carries no `ℝ≥0∞` division and is honest at `λ = 0`, where it is
vacuous — exactly as CV's bound `M·t/λ` is vacuous there.

This is `mul_lintegral_inv_ell_ellProb_le_one` (`HoldingTime.lean`) with the smoothness
parameter `1 - s` replaced by a free `λ`.  It is proved directly rather than by instantiating
that lemma at `s := 1 - λ`, because `ℝ≥0∞` truncated subtraction only satisfies
`1 - (1 - λ) = λ` when `λ ≤ 1`, and no such restriction belongs in this statement. -/
theorem mul_lintegral_inv_ell_ellProb_le_one_of_le_avg {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {lam : ℝ≥0∞} (hlam : lam ≤ avgLocalConductance K δ) :
    lam * ∫⁻ x, (ell K δ x)⁻¹ ∂(ellProb K δ) ≤ 1 := by
  have hL0 : ellMeasure K δ Set.univ ≠ 0 := ellMeasure_univ_ne_zero hK hK0 hδ
  have hLtop : ellMeasure K δ Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (ellMeasure_univ_le K δ)
  have hmul : lam * volume K ≤ ellMeasure K δ Set.univ :=
    mul_volume_le_ellMeasure_univ_of_le_avg hK0 hKtop hlam
  rw [lintegral_inv_ell_ellProb hK hδ]
  calc lam * ((ellMeasure K δ Set.univ)⁻¹ * volume K)
      = (ellMeasure K δ Set.univ)⁻¹ * (lam * volume K) := by ring
    _ ≤ (ellMeasure K δ Set.univ)⁻¹ * ellMeasure K δ Set.univ := by gcongr
    _ = 1 := ENNReal.inv_mul_cancel hL0 hLtop

/-! ## 3. `lem:speedy-to-ball`

Ingredient (i) — warmth along the chain — is §1; ingredient (ii) — the stationary cost `1/λ`
— is §2.  CV's proof is their product, and so is this. -/

/-- **Cousins–Vempala `lem:speedy-to-ball`** (`vol3_journal.tex:915`), core form:

    λ · ∑_{i<t} ∫⁻ (ell K δ)⁻¹ d(iterate (speedyWalk K δ) Q₀ i)  ≤  t · M.

In words: if the average local conductance is at least `λ` and the speedy walk is started
from a law that is `M`-warm for the speedy walk's own stationary law `ellProb K δ`, then the
total mean holding time accumulated over `t` speedy steps is at most `M·t/λ`.

Assumes `MeasurableSet K`, `δ > 0`, `0 < vol K < ⊤`, `hlam : λ ≤ avgLocalConductance K δ`
(CV's `lem:lambda-bound`, **assumed, not proved** — see the module docstring) and
`hwarm : IsWarm M Q₀ (ellProb K δ)` (CV's `M(Q₀,Q) ≤ M`).

Stated multiplicatively: `λ` may be `0`, in which case both CV's bound and this one are
vacuous.  `sum_lintegral_inv_ell_iterate_speedyWalk_le` is the divided form.

**Scope.**  The summand `∫⁻ (ell K δ)⁻¹ dQᵢ` is the mean, under the law of the current speedy
state, of the ball walk's holding time — and that holding time is a *proved* expected exit
time of the real trajectory, which is what
`mul_sum_lintegral_exitTime_iterate_speedyWalk_le` records.  The sum is therefore CV's
linearity-of-expectation quantity exactly.  It is **not** proved equal to the number of steps
a single ball-walk trajectory takes to realise `t` speedy steps; that identification is the
path-level time change, unproved here and in `TrajTransfer.lean` (its "What is not proved",
item 1). -/
theorem mul_sum_lintegral_inv_ell_iterate_speedyWalk_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {lam M : ℝ≥0∞} (hlam : lam ≤ avgLocalConductance K δ)
    {Q₀ : Measure (EuclideanSpace ℝ (Fin n))} (hwarm : IsWarm M Q₀ (ellProb K δ)) (t : ℕ) :
    lam * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x)⁻¹ ∂(iterate (speedyWalk K δ) Q₀ i)
      ≤ (t : ℝ≥0∞) * M := by
  have hstat : step (speedyWalk K δ) (ellProb K δ) = ellProb K δ :=
    step_invariant (invariant_speedyWalk hK δ)
  have hsum := sum_lintegral_iterate_le_of_isWarm hwarm hstat (fun x => (ell K δ x)⁻¹) t
  have havg := mul_lintegral_inv_ell_ellProb_le_one_of_le_avg hK hδ hK0 hKtop hlam
  calc lam * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x)⁻¹ ∂(iterate (speedyWalk K δ) Q₀ i)
      ≤ lam * ((t : ℝ≥0∞) * (M * ∫⁻ x, (ell K δ x)⁻¹ ∂(ellProb K δ))) := by gcongr
    _ = (t : ℝ≥0∞) * M * (lam * ∫⁻ x, (ell K δ x)⁻¹ ∂(ellProb K δ)) := by ring
    _ ≤ (t : ℝ≥0∞) * M * 1 := by gcongr
    _ = (t : ℝ≥0∞) * M := mul_one _

/-- **The divided form**, `∑ ≤ t·M/λ`, which is CV's `M·t/λ` verbatim.

Assumes everything `mul_sum_lintegral_inv_ell_iterate_speedyWalk_le` assumes, plus `λ ≠ 0`
and `λ ≠ ⊤` — the two guards `ℝ≥0∞` division needs for the quotient to carry the same
information as the product.  Both are discharged in `exists_wastedSteps_witness`. -/
theorem sum_lintegral_inv_ell_iterate_speedyWalk_le {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {lam M : ℝ≥0∞} (hlam : lam ≤ avgLocalConductance K δ) (hlam0 : lam ≠ 0) (hlamtop : lam ≠ ⊤)
    {Q₀ : Measure (EuclideanSpace ℝ (Fin n))} (hwarm : IsWarm M Q₀ (ellProb K δ)) (t : ℕ) :
    ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x)⁻¹ ∂(iterate (speedyWalk K δ) Q₀ i)
      ≤ (t : ℝ≥0∞) * M / lam := by
  refine (ENNReal.le_div_iff_mul_le (Or.inl hlam0) (Or.inl hlamtop)).2 ?_
  rw [mul_comm]
  exact mul_sum_lintegral_inv_ell_iterate_speedyWalk_le hK hδ hK0 hKtop hlam hwarm t

/-! ## 4. The same bound about the real ball-walk trajectory

`lintegral_exitTime_pathMeasure_ballWalk` (`TrajTransfer.lean`) proves that the mean, under
the *trajectory measure* of the ball walk started at `x`, of the exit time
`inf {i | ωᵢ ≠ x}` — the number of ball-walk steps up to and including the first proper one —
is exactly `(ell K δ x)⁻¹`.  Averaging that identity over the law of the current speedy state
turns §3's formal reciprocal into a statement about ball-walk step counts. -/

/-- **The averaged mean-holding-time identity.**  For any law `μ` of the starting point,

    ∫⁻ x, E_x[exit time of the ball walk from x] dμ = ∫⁻ x, (ell K δ x)⁻¹ dμ,

where the inner expectation is taken under the ball walk's trajectory measure started at the
Dirac mass at `x`, and the exit time is written in its tail-sum form
`∑ₖ 1[ω has not left x by time k]` (which is `inf {i | ωᵢ ≠ x}` pointwise).

Assumes `MeasurableSet K` and `[NeZero n]`; both are inherited from
`lintegral_exitTime_pathMeasure_ballWalk`, and `[NeZero n]` is not removable — in
`EuclideanSpace ℝ (Fin 0)` the space is a single atom.  No hypothesis on `μ` at all: the
identity is pointwise in `x`, so it integrates against anything.

This is CV's "for any point `x`, the expected number of steps until a proper step is made is
`1/ℓ(x)`" (`vol3_journal.tex:931`), in the form the cost sum consumes it. -/
theorem lintegral_lintegral_exitTime_pathMeasure_ballWalk [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    ∫⁻ x, (∫⁻ ω, (∑' k : ℕ, {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
              (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω)
            ∂(pathMeasure (ballWalk K δ) (Measure.dirac x))) ∂μ
      = ∫⁻ x, (ell K δ x)⁻¹ ∂μ :=
  lintegral_congr fun x => lintegral_exitTime_pathMeasure_ballWalk hK δ x

/-- **Cousins–Vempala `lem:speedy-to-ball`, trajectory form** — the headline of this file:

    λ · ∑_{i<t} ∫⁻ x, E_x[ball-walk exit time from x] d(iterate (speedyWalk K δ) Q₀ i)
      ≤ t · M.

Identical to `mul_sum_lintegral_inv_ell_iterate_speedyWalk_le` except that the integrand is
the *proved* expected number of ball-walk steps until a proper step is made, computed under
the ball walk's own trajectory measure, rather than the reciprocal `(ell K δ x)⁻¹`.  So each
summand is a genuine expected ball-walk step count, and the sum is exactly the quantity CV
bound by linearity of expectation.

Assumes `MeasurableSet K`, `δ > 0`, `0 < vol K < ⊤`, `[NeZero n]`, `hlam` (CV's
`lem:lambda-bound`, **assumed, not proved**) and `hwarm` (CV's `M(Q₀,Q) ≤ M`).

**What this still does not say**: that a single ball-walk trajectory realising `t` speedy
steps takes at most `M·t/λ` steps.  Passing from the sum of per-step conditional expectations
to a functional of one trajectory is the path-level time change `ω_t = Y_{N t}`, which is
`TrajTransfer.lean`'s unproved item 1.  No running-time claim is made or implied. -/
theorem mul_sum_lintegral_exitTime_iterate_speedyWalk_le [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) {δ : ℝ} (hδ : 0 < δ)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {lam M : ℝ≥0∞}
    (hlam : lam ≤ avgLocalConductance K δ) {Q₀ : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm M Q₀ (ellProb K δ)) (t : ℕ) :
    lam * ∑ i ∈ Finset.range t,
        ∫⁻ x, (∫⁻ ω, (∑' k : ℕ, {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
                  (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω)
                ∂(pathMeasure (ballWalk K δ) (Measure.dirac x)))
          ∂(iterate (speedyWalk K δ) Q₀ i)
      ≤ (t : ℝ≥0∞) * M := by
  simp_rw [lintegral_lintegral_exitTime_pathMeasure_ballWalk hK δ]
  exact mul_sum_lintegral_inv_ell_iterate_speedyWalk_le hK hδ hK0 hKtop hlam hwarm t

/-! ## 5. Non-vacuity

`CLAUDE.md` §11: a theorem whose hypotheses nothing satisfies certifies nothing.  The unit
ball with any `δ > 0`, started at stationarity, satisfies every binder above with `λ` non-zero
and finite and `M = 1` — and attains the bound with equality, so the conclusion is not
degenerate either. -/

/-- **The non-vacuity witness.**  For every dimension `n ≥ 1`, every step `δ > 0` and every
`t ≥ 1` there are a body `K` — the unit ball — a start `Q₀`, a `λ` and an `M` such that

* `K` is measurable with `0 < vol K < ⊤`, so `ballWalk K δ` and `speedyWalk K δ` are the real
  kernels and `ellProb K δ` is a genuine probability measure;
* `λ ≠ 0` and `λ ≠ ⊤`, so the divided form
  `sum_lintegral_inv_ell_iterate_speedyWalk_le` applies and its right-hand side is a real
  number rather than `⊤`;
* `hlam : λ ≤ avgLocalConductance K δ` holds — with `λ` the *exact* average local
  conductance, so the witness makes no concession on this hypothesis;
* `hwarm : IsWarm M Q₀ (ellProb K δ)` holds with `M = 1`, the best possible warmness;
* the left-hand sum is **strictly positive and finite**, so the bound is not the vacuous
  `0 ≤ anything`;
* the bound holds **with equality**, `λ · ∑ = t · M`, in both the core form and the
  trajectory form.  The bound of `lem:speedy-to-ball` is therefore *attained*, by the speedy
  walk started at its own stationary law.

`[NeZero n]` is needed only for the trajectory-form conjunct, which is where
`TrajTransfer.lean`'s hypothesis lives. -/
theorem exists_wastedSteps_witness [NeZero n] {δ : ℝ} (hδ : 0 < δ) {t : ℕ} (ht : 1 ≤ t) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (Q₀ : Measure (EuclideanSpace ℝ (Fin n)))
      (lam M : ℝ≥0∞),
      MeasurableSet K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
        IsProbabilityMeasure (ellProb K δ) ∧ IsProbabilityMeasure Q₀ ∧
        lam ≠ 0 ∧ lam ≠ ⊤ ∧ M = 1 ∧
        lam ≤ avgLocalConductance K δ ∧ IsWarm M Q₀ (ellProb K δ) ∧
        0 < ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x)⁻¹ ∂(iterate (speedyWalk K δ) Q₀ i) ∧
        (∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x)⁻¹ ∂(iterate (speedyWalk K δ) Q₀ i)) ≠ ⊤ ∧
        lam * ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x)⁻¹ ∂(iterate (speedyWalk K δ) Q₀ i)
          = (t : ℝ≥0∞) * M ∧
        lam * ∑ i ∈ Finset.range t,
            ∫⁻ x, (∫⁻ ω, (∑' k : ℕ,
                    {ω' : ℕ → EuclideanSpace ℝ (Fin n) | ∀ i ≤ k, ω' i = x}.indicator
                      (1 : (ℕ → EuclideanSpace ℝ (Fin n)) → ℝ≥0∞) ω)
                  ∂(pathMeasure (ballWalk K δ) (Measure.dirac x)))
              ∂(iterate (speedyWalk K δ) Q₀ i)
          = (t : ℝ≥0∞) * M := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 1 with hKdef
  have hK : MeasurableSet K := measurableSet_ball
  have hK0 : volume K ≠ 0 := volume_unitBall_ne_zero
  have hKtop : volume K ≠ ⊤ := volume_unitBall_ne_top
  have hL0 : ellMeasure K δ Set.univ ≠ 0 := ellMeasure_univ_ne_zero hK hK0 hδ
  have hLtop : ellMeasure K δ Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (ellMeasure_univ_le K δ)
  have hprob : IsProbabilityMeasure (ellProb K δ) := isProbabilityMeasure_ellProb hL0 hLtop
  -- the chain started at stationarity stays there
  have hiter : ∀ i : ℕ, iterate (speedyWalk K δ) (ellProb K δ) i = ellProb K δ :=
    iterate_invariant (step_invariant (invariant_speedyWalk hK δ))
  -- the cost sum, computed exactly
  have hsum : ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x)⁻¹ ∂(iterate (speedyWalk K δ) (ellProb K δ) i)
      = (t : ℝ≥0∞) * ((ellMeasure K δ Set.univ)⁻¹ * volume K) := by
    simp_rw [hiter, lintegral_inv_ell_ellProb hK hδ]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have ht0 : (t : ℝ≥0∞) ≠ 0 := by
    simpa using Nat.one_le_iff_ne_zero.1 ht
  refine ⟨K, ellProb K δ, avgLocalConductance K δ, 1, hK, hK0, hKtop, hprob, hprob, ?_, ?_, rfl,
    le_rfl, IsWarm.refl _, ?_, ?_, ?_, ?_⟩
  · -- `λ ≠ 0`
    rw [avgLocalConductance, ← ellMeasure_univ]
    intro hcon
    rcases ENNReal.div_eq_zero_iff.1 hcon with h | h
    · exact hL0 h
    · exact hKtop h
  · -- `λ ≠ ⊤`
    rw [avgLocalConductance, ← ellMeasure_univ]
    intro hcon
    rcases ENNReal.div_eq_top.1 hcon with ⟨-, h⟩ | ⟨h, -⟩
    · exact hK0 h
    · exact hLtop h
  · -- the sum is positive
    rw [hsum]
    exact ENNReal.mul_pos ht0 (ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hLtop) hK0).ne'
  · -- the sum is finite
    rw [hsum]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hL0) hKtop)
  · -- equality, core form
    rw [hsum, avgLocalConductance, ← ellMeasure_univ, ENNReal.div_eq_inv_mul, mul_one]
    calc (volume K)⁻¹ * ellMeasure K δ Set.univ
          * ((t : ℝ≥0∞) * ((ellMeasure K δ Set.univ)⁻¹ * volume K))
        = (t : ℝ≥0∞) * ((ellMeasure K δ Set.univ * (ellMeasure K δ Set.univ)⁻¹)
            * ((volume K)⁻¹ * volume K)) := by ring
      _ = (t : ℝ≥0∞) := by
          rw [ENNReal.mul_inv_cancel hL0 hLtop, ENNReal.inv_mul_cancel hK0 hKtop, one_mul,
            mul_one]
  · -- equality, trajectory form
    simp_rw [lintegral_lintegral_exitTime_pathMeasure_ballWalk hK δ]
    rw [hsum, avgLocalConductance, ← ellMeasure_univ, ENNReal.div_eq_inv_mul, mul_one]
    calc (volume K)⁻¹ * ellMeasure K δ Set.univ
          * ((t : ℝ≥0∞) * ((ellMeasure K δ Set.univ)⁻¹ * volume K))
        = (t : ℝ≥0∞) * ((ellMeasure K δ Set.univ * (ellMeasure K δ Set.univ)⁻¹)
            * ((volume K)⁻¹ * volume K)) := by ring
      _ = (t : ℝ≥0∞) := by
          rw [ENNReal.mul_inv_cancel hL0 hLtop, ENNReal.inv_mul_cancel hK0 hKtop, one_mul,
            mul_one]

/-! ## Axiom audit

Every theorem of this file, re-checked at elaboration time.  Each must print exactly
`[propext, Classical.choice, Quot.sound]`; anything else — in particular `sorryAx` — means
the file is not finished. -/

#print axioms lintegral_le_of_isWarm
#print axioms lintegral_iterate_le_of_isWarm
#print axioms sum_lintegral_iterate_le_of_isWarm
#print axioms lintegral_inv_ell_ellProb
#print axioms mul_volume_le_ellMeasure_univ_of_le_avg
#print axioms mul_lintegral_inv_ell_ellProb_le_one_of_le_avg
#print axioms mul_sum_lintegral_inv_ell_iterate_speedyWalk_le
#print axioms sum_lintegral_inv_ell_iterate_speedyWalk_le
#print axioms lintegral_lintegral_exitTime_pathMeasure_ballWalk
#print axioms mul_sum_lintegral_exitTime_iterate_speedyWalk_le
#print axioms exists_wastedSteps_witness

end Arlib.MarkovChains
