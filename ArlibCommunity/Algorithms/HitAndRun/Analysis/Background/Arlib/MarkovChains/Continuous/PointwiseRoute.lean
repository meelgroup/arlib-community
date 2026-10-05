/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.PointwiseMixing
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.MixingFromConductance
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.UniformOn
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.KV97.Theorem2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Closing the TV → pointwise gap: which route actually works

`Arlib/MarkovChains/Continuous/PointwiseMixing.lean` proves that a total-variation bound
**never** implies a pointwise density bound — for every TV tolerance `δ ≠ 0` there is no `ε`
at all making `TVLe μ ν δ → PointwiseClose μ ν ε`
(`Arlib.MarkovChains.not_exists_pointwiseClose_of_tvLe`) — and that the ball walk is not
uniformly minorised, because it is *local*.  That closed off "run the walk until it mixes,
then quote a pointwise error".  Its docstring named three candidate routes.  This file
evaluates all three and formalises the one that works.

## Verdict

**Route 3 wins, and `AUDIT-KV97.md` §4b's dismissal of it is wrong.**  §4b is right that a
TV hypothesis buys only an *additive* error; it is wrong that this makes the theorem
useless.  The whole argument is one line of algebra, `Arlib.PointwiseRoute.window_of_tvLe`:

> an additive error `ε` **is** a relative error `ε · V`.

So a TV tolerance of `θ / Vol(P')` — not `θ` — delivers exactly the two-sided window
`(1 − (E+θ))/V ≤ Pr[rnd p = x] ≤ (1+θ)/V` that Kannan–Vempala's Theorem 2 needs, and the
`ε`s in `cor:linf` then cancel (`ratio_bounds_of_tvLe`).  §4b's objection — "summing over
the `N` lattice points contributes `N·ε`, which does not cancel" — evaporates: at
`ε = θ/V` the sum contributes `Nθ/V` against a total of about `N/V`, i.e. a *relative*
`θ`.  That is `ratio_bounds_of_tvLe`, which is proved here.

The remaining question is whether asking for `ε = θ/V` is affordable, and it is, because
**mixing time is logarithmic in the TV tolerance**.  `conductanceMixingTime_inv_volume_le`
makes this quantitative: reaching TV `θ/V` costs

  `(log M + 2·log V + 2·log(1/θ)) / φ² + 1`

steps — *linear in `log V`*, not in `V`.  For the KV97 application `V = Vol(P')` with `P'`
the `10^ρ`-dilated inflated polytope, `log V = O(n·(ρ + log R))`: **polynomial in `n·ρ`**,
which is the bit-length of the `10^{−ρ}`-discretised description and precisely the quantity
the rest of the algorithm is already polynomial in.  The price of the whole TV → pointwise
gap is therefore one factor of `O(nρ)` in the step count.  §4b's "which no sampler
delivers" confuses `ε` being *exponentially small as a number* with its being *expensive to
achieve*; it is the first and not the second, because the number of steps is logarithmic
in `1/ε`.

**Route 3 is also the only route that can work *for the ball walk***, for a reason neither
the audit nor `PointwiseMixing.lean` noticed: `PointwiseClose` and
`Arlib.KV97.PointwiseAlmostUniform` both presuppose the sampler's law **has a density**.  A
ball-walk law started at a point does not: the holding term `(1 − ℓ(x))·δ_x` of
`Arlib.MarkovChains.ballWalk_apply_set` keeps an atom of mass `∏(1 − ℓ)` forever.
`not_pointwiseClose_of_atom` below shows one atom destroys pointwise closeness for **every**
`ε`, `⊤` included, at **every** finite time, and `exists_tvLe_with_atom` shows a
total-variation bound has no such defect.  So for the chain the programme actually runs,
from a point start, the pointwise hypothesis is not merely hard to obtain from mixing — it
is *false*.  (Route 2 does produce a law with a density; it is expensive, not impossible.)

## Route 1 (local Harnack / smoothing): sound but unnecessary, and unsupported

The mathematics is real.  After a ball-walk step the density is
`f_{t+1}(y) = (1 − ℓ(y))·f_t(y) + (vol B_δ)⁻¹ ∫_{B(y,δ)∩K} f_t`, whose second term is
Lipschitz in `y` with constant `O(‖f_t‖_∞ · n/δ)`; on speedy points `ℓ ≥ 3/4` kills the
first term geometrically.  Combining "`‖f − 1‖₁` small" with "`f − 1` is `L`-Lipschitz"
gives `‖f − 1‖_∞ ≲ (L^n ‖f − 1‖₁)^{1/(n+1)}` by the usual ball-volume interpolation.  That
is a genuine TV → `L^∞` upgrade.

But (a) it needs a TV error of order `ε^{n+1}(δ/n)^n`, i.e. `log(1/ε_TV) = Θ(n log n)` —
**the same `O(n)` factor in the step count that route 3 pays**, so it buys nothing; and
(b) Mathlib v4.32 has no Harnack inequality, no elliptic regularity, no Sobolev embedding
and no `L¹`–`L^∞` interpolation to build it on (`grep -ri harnack Mathlib/` is empty; there
is no `Mathlib/Analysis/PDE/`).  It would be several thousand lines of new analysis to
reach a conclusion route 3 reaches in twenty.  **Do not pursue route 1.**

## Route 2 (rejection against an exact proposal): correct, and exponentially expensive

Route 2 is *formalised in full* below, because it is the non-vacuity witness for the whole
pointwise interface: rejection really does give `ε = 0`.
`condOn_uniformOn_eq_uniformOn` proves the general lemma

  `S ⊆ B  ⟹  condOn (uniformOn μ B) S = uniformOn μ S`,

*exactly* uniform, with acceptance probability `μ S / μ B` (`uniformOn_acceptance`), and
`pointwiseAlmostUniform_of_rejection` hands the result straight to `Arlib.KV97.theorem2` at
`ε = 0`.

But there is **no polynomial regime**, and `roundBody` / isotropic position does not create
one.  The best a rounding transformation guarantees is a sandwich `B(0,1) ⊆ K ⊆ B(0,R)`
with `R = Θ(√n)`.  `uniformOn_ball_ball` computes, **exactly**, the acceptance rate for the
extremal member of that family, `K = B(0,1)`: it is `(1/R)^n`.  So the sandwich hypothesis
by itself permits no acceptance guarantee better than `R^{-n}`, and at `R = Θ(√n)` that is
`n^{−n/2}` — superexponentially small.  Rejection from a *box* is no better (not formalised
here): the cube circumscribing `B(0,1)` has volume `2^n` against the ball's `(2πe/n)^{n/2}`,
the same `n`-th-power loss.
`Ttc/Witness/BoxProb.lean` gets away with rejection precisely because its `P'` *is* the
proposal box, so `B = P'` and the acceptance rate is `1`; that is a witness, not an
algorithm.

## What the downstream interface became

**This refactor has since been performed.**  `Ttc.KV97Sampler`
(`Ttc/Model/ProblemSetting.lean`) formerly carried `contDensity`, `contVol`,
`density_au : PointwiseAlmostUniform (contDensity i) … (epsPrime/4)`.  On route 3 those
became

* `contLaw : … → Measure (Space n)` with `[IsProbabilityMeasure (contLaw i)]` — the law the
  chain actually reaches, which need not have a density;
* `law_tv : ∀ i, TVLe (contLaw i) (uniformOn volume (inflated …))
    (ENNReal.ofReal (epsPrime / (4 * contVol i)))` — **the tolerance carries the `1/V`**;

and `sampD_eq`'s numerator `∫ p in P', contDensity i p * prodTent (…) p` becomes
`∫ p, prodTent (…) p ∂(contLaw i)`.  `theorem2_of_tvLe_inv_volume` then discharges exactly
what `density_au` used to, and `ratio_bounds_of_tvLe` replaces the `cor:linf` step.  The
resulting window is the same shape; its lower constant is `1 − (E + θ)` where the pointwise
route gives `(1 − θ)(1 − E)`, i.e. weaker by `θE`, which is negligible.

That refactor is **not** performed here — `Ttc/Model/ProblemSetting.lean` belongs to another
agent — but every lemma it needs is in this file.

## What is proved here

* `window_of_tvLe` — **the crux.**  An additive TV error `ε` on a `[0,1]`-observable whose
  reference average sits in `[(1−a)/V, (1+b)/V]` moves that window to
  `[(1−(a+θ))/V, (1+(b+θ))/V]` for any `θ ≥ ε·V`.  Additive becomes relative at scale `V`.
* `window_of_tvLe_inv_volume` — the same with the tolerance written as `θ/V`.
* `theorem2_of_tvLe`, `theorem2_of_tvLe_inv_volume` — **Kannan–Vempala Theorem 2, re-derived
  from a total-variation hypothesis**, in measure form (`∫ prodTent x p ∂μ`, which needs no
  density and so applies to laws with atoms).
* `ratio_bounds_of_tvLe` — **the refutation of §4b**: the `cor:linf` ratio window, from a TV
  hypothesis.  The `ε`s cancel.
* `theorem2_of_mixesWithin` — the end-to-end statement: a chain mixed to TV `θ/V` satisfies
  Theorem 2's conclusion.
* `conductanceMixingTime_inv_volume_le` — the cost, `O(φ⁻²(log M + log V + log(1/θ)))`.
* `not_pointwiseClose_of_atom`, `not_pointwiseClose_uniformOn_of_atom` — why the pointwise
  hypothesis cannot be met by a chain started at a point.
* `exists_tvLe_with_atom` — the contrast: a law with an atom of mass `δ` that is still
  within total variation `δ` of the target.  TV tolerates what pointwise cannot.
* `condOn_uniformOn_eq_uniformOn`, `uniformOn_acceptance`,
  `pointwiseClose_condOn_uniformOn`, `integral_uniformOn_eq_setIntegral_const_mul`,
  `pointwiseAlmostUniform_of_rejection` — route 2, in full.
* `uniformOn_ball_ball`, `uniformOn_ball_ball_one`, `uniformOn_ball_ball_euclidean` —
  route 2's price, exactly `(r/R)^n`.
* `exists_theorem2_of_tvLe_witness` — the non-vacuity witness (`CLAUDE.md` §11) for
  `theorem2_of_tvLe_inv_volume`'s hypothesis bundle.

## What this does NOT close, stated plainly

* **The conductance / isoperimetry bound is still owed.**  Everything here consumes a
  `TVLe` or a `MixesWithin`; nothing here produces one.  Proving the ball walk (or speedy
  walk) has conductance `φ ≥ 1/poly` is the remaining programme, and route 3 neither helps
  nor hinders it.  `theorem2_of_mixesWithin` is exactly the socket that bound plugs into.
* **`log V` is polynomial only in the size of the *discretised* description.**  `log V` is
  `Θ(n·ρ)` where `10^{−ρ}` is the lattice spacing.  If `ρ` were handed over in binary and
  the output were not itself `Θ(nρ)` bits, this would be exponential in the encoding.  It is
  not: the algorithm's answer is a count of `10^{−ρ}`-lattice points, so `n·ρ` is the honest
  size parameter.  Stated so an auditor can disagree.
* **The `ρ`-dependence is additive in the step count, not multiplicative in the accuracy.**
  `conductanceMixingTime_inv_volume_le` adds `2·log V / φ²`; it does not multiply.

## Scope

**No new predicate is introduced.**  Every statement is about `Arlib.TVLe`,
`Arlib.uniformOn`, `Arlib.condOn`, `Arlib.MarkovChains.PointwiseClose` and
`Arlib.KV97.PointwiseAlmostUniform` as they already stand; nothing here defines a class
whose fields assume the conclusion.  Nothing here proves the ball walk mixes — that is the
conductance/isoperimetry programme, untouched.  What is proved is that *once* it mixes, in
total variation, to tolerance `θ/Vol(P')`, the pointwise hypothesis of
`Arlib.KV97.theorem2` is no longer needed at all.
-/

namespace Arlib.PointwiseRoute

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

/-! ## Route 3, the crux: an additive error is a relative error at scale `V`

`Arlib.TVLe.integral_le` is the honest additive transfer: for `0 ≤ g ≤ 1`,
`|∫ g dμ − ∫ g dν| ≤ ε`.  `AUDIT-KV97.md` §4b reads that as fatal because the quantity being
bounded is of size `1/V` with `V` enormous.  It is fatal only if `ε` is held fixed.  The
lemma below is the whole of the answer: the *relative* error is `ε·V`, so the tolerance one
must ask the sampler for is `θ/V`, and nothing else changes. -/

/-- **The crux.**  Let `μ` be within total variation `ε` of `ν`, let `g` be a measurable
observable with `0 ≤ g ≤ 1`, and suppose its `ν`-average lies in the window
`[(1−a)/V, (1+b)/V]`.  Then its `μ`-average lies in `[(1−(a+θ))/V, (1+(b+θ))/V]` for any
`θ ≥ ε·V`.

**An additive error `ε` is a relative error `ε·V`.**  This is the sentence `AUDIT-KV97.md`
§4b is missing.  The additive transfer is not weaker than the relative one; it is the same
statement with the error measured in a different unit, and converting the unit costs a
factor of `V` in the *tolerance*, hence only `log V` in the *mixing time*
(`conductanceMixingTime_inv_volume_le`). -/
theorem window_of_tvLe {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε : ℝ≥0∞} {V a b θ : ℝ}
    {g : Ω → ℝ} (htv : TVLe μ ν ε) (hεtop : ε ≠ ⊤) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) (hV : 0 < V) (hεV : ε.toReal * V ≤ θ)
    (hlo : (1 - a) / V ≤ ∫ x, g x ∂ν) (hhi : ∫ x, g x ∂ν ≤ (1 + b) / V) :
    (1 - (a + θ)) / V ≤ ∫ x, g x ∂μ ∧ ∫ x, g x ∂μ ≤ (1 + (b + θ)) / V := by
  have habs := htv.integral_le hεtop hg hg0 hg1
  rw [abs_sub_le_iff] at habs
  have ht : ε.toReal ≤ θ / V := (le_div_iff₀ hV).2 hεV
  have e1 : (1 - (a + θ)) / V = (1 - a) / V - θ / V := by
    rw [div_sub_div_same]; ring_nf
  have e2 : (1 + (b + θ)) / V = (1 + b) / V + θ / V := by
    rw [← add_div]; ring_nf
  refine ⟨?_, ?_⟩
  · rw [e1]; linarith [habs.2]
  · rw [e2]; linarith [habs.1]

/-- **The crux, with the tolerance named.**  Asking the sampler for total variation
`θ / V` — rather than `θ` — turns the additive transfer into the relative window
`[(1−(a+θ))/V, (1+(b+θ))/V]`.  This is the hypothesis a mixing bound should be run to. -/
theorem window_of_tvLe_inv_volume {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {V a b θ : ℝ} {g : Ω → ℝ}
    (htv : TVLe μ ν (ENNReal.ofReal (θ / V))) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∀ x, g x ≤ 1) (hV : 0 < V) (hθ : 0 ≤ θ)
    (hlo : (1 - a) / V ≤ ∫ x, g x ∂ν) (hhi : ∫ x, g x ∂ν ≤ (1 + b) / V) :
    (1 - (a + θ)) / V ≤ ∫ x, g x ∂μ ∧ ∫ x, g x ∂μ ≤ (1 + (b + θ)) / V := by
  refine window_of_tvLe htv ENNReal.ofReal_ne_top hg hg0 hg1 hV ?_ hlo hhi
  rw [ENNReal.toReal_ofReal (by positivity), div_mul_cancel₀ _ hV.ne']

/-! ## Route 3, applied: the `cor:linf` ratio window

`AUDIT-KV97.md` §4b's second bullet is the one that looks decisive: "summing an additive
`ε` over the `N` lattice points contributes `N·ε`, which does not cancel and does not
vanish."  It is answered by substituting `ε = θ/V`.  The `N` weights are then pinned in a
`(1 ± θ)/V` window, `Arlib.Rejection.ratio_bounds_of_window` applies verbatim, and `V` — the
enormous quantity — cancels out of the ratio entirely. -/

/-- **The refutation of `AUDIT-KV97.md` §4b, bullet 2.**  From a *total-variation*
hypothesis at tolerance `ε` with `ε·V ≤ θ`, the normalised weights `∫ gᵢ dμ / ∑ⱼ ∫ gⱼ dμ`
lie in the relative window

  `[(1−(a+θ)) / ((1+(b+θ))·N),  (1+(b+θ)) / ((1−(a+θ))·N)]`.

`V` has cancelled.  The `ε`s do cancel; §4b's `N·ε` is `Nθ/V` against a total of order
`N/V`, i.e. a relative `θ`.  This is `Arlib.KV97.cor_linf`'s conclusion obtained without any
pointwise hypothesis at all. -/
theorem ratio_bounds_of_tvLe {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    [Nonempty ι] {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ≥0∞} {V a b θ : ℝ} {g : ι → Ω → ℝ} (htv : TVLe μ ν ε) (hεtop : ε ≠ ⊤)
    (hg : ∀ i, Measurable (g i)) (hg0 : ∀ i x, 0 ≤ g i x) (hg1 : ∀ i x, g i x ≤ 1)
    (hV : 0 < V) (hεV : ε.toReal * V ≤ θ) (hlo : ∀ i, (1 - a) / V ≤ ∫ x, g i x ∂ν)
    (hhi : ∀ i, ∫ x, g i x ∂ν ≤ (1 + b) / V) (hab : a + θ < 1) (i : ι) :
    (1 - (a + θ)) / ((1 + (b + θ)) * (Fintype.card ι : ℝ))
        ≤ (∫ x, g i x ∂μ) / (∑ j, ∫ x, g j x ∂μ) ∧
      (∫ x, g i x ∂μ) / (∑ j, ∫ x, g j x ∂μ)
        ≤ (1 + (b + θ)) / ((1 - (a + θ)) * (Fintype.card ι : ℝ)) :=
  Rejection.ratio_bounds_of_window (fun j => ∫ x, g j x ∂μ) hV hab
    (fun j => (window_of_tvLe htv hεtop (hg j) (hg0 j) (hg1 j) hV hεV (hlo j) (hhi j)).1)
    (fun j => (window_of_tvLe htv hεtop (hg j) (hg0 j) (hg1 j) hV hεV (hlo j) (hhi j)).2) i

/-! ## Route 3 applied: Kannan–Vempala Theorem 2 from a total-variation hypothesis

`Arlib.KV97.theorem2` takes a *density* `f` and computes `Pr[rnd p = x]` as
`∫_{P'} f p · prodTent x p dp`.  The statements below take the sampler's **law** `μ` and
compute the same quantity as `∫ prodTent x p ∂μ`.  The measure form is the primitive one —
a sampler returns a law, not a density — and it is strictly more general: a law with an
atom has no density at all, and `not_pointwiseClose_of_atom` below shows that is exactly
the situation of a ball walk started at a point.

The two forms agree whenever the law does have a density; for the uniform law this is
`integral_prodTent_uniformOn_eq_setIntegral` below, which is also the bridge route 2 uses. -/

section KV97

open Arlib.Lattice.Rounding

variable {n : ℕ}

/-- The rounding kernel is bounded by `1`: it is a product of `tent` values, and
`tent u = max (1 − |u|) 0 ≤ 1`.  This is what makes `Arlib.TVLe.integral_le` applicable to
it — that lemma transfers `[0,1]`-valued observables, and `Arlib.Lattice.Rounding` records
only `prodTent_nonneg`. -/
theorem prodTent_le_one (x p : EuclideanSpace ℝ (Fin n)) : prodTent x p ≤ 1 := by
  have h : ∀ i : Fin n, tent (p i - x i) ≤ 1 := by
    intro i
    have habs := abs_nonneg (p i - x i)
    simp only [tent]
    exact max_le (by linarith) zero_le_one
  simp only [prodTent]
  exact Finset.prod_le_one (fun i _ => tent_nonneg _) fun i _ => h i

/-- The uniform average of the rounding kernel is the set integral over `S`, scaled by the
volume.  `Arlib.integral_uniformOn_real`, specialised. -/
theorem integral_prodTent_uniformOn (S : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫ p, prodTent x p ∂(uniformOn volume S)
      = (volume S).toReal⁻¹ * ∫ p in S, prodTent x p :=
  integral_uniformOn_real volume S (prodTent x)

/-- **The reference window.**  Under the *exactly* uniform law on `S`, `Pr[rnd p = x]` sits
in `[(1−E)/V, 1/V]`, where `E` bounds the escape mass.  This is Kannan–Vempala's Theorem 2
at `ε = 0`, and it is the window the total-variation transfer then widens by `θ`. -/
theorem uniformOn_window {S : Set (EuclideanSpace ℝ (Fin n))} {V E : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hS : MeasurableSet S) (hVS : (volume S).toReal = V)
    (hV : 0 < V) (hesc : ∫ p in Sᶜ, prodTent x p ≤ E) :
    (1 - E) / V ≤ ∫ p, prodTent x p ∂(uniformOn volume S) ∧
      ∫ p, prodTent x p ∂(uniformOn volume S) ≤ (1 + 0) / V := by
  have hinside : 1 - E ≤ ∫ p in S, prodTent x p := by
    rw [setIntegral_prodTent_compl x hS]; linarith
  have hle : ∫ p in S, prodTent x p ≤ 1 := setIntegral_prodTent_le_one x hS
  have hval : ∫ p, prodTent x p ∂(uniformOn volume S) = V⁻¹ * ∫ p in S, prodTent x p := by
    rw [integral_prodTent_uniformOn, hVS]
  have hinv : (0 : ℝ) ≤ V⁻¹ := inv_nonneg.2 hV.le
  constructor
  · rw [hval, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hinside hinv
  · rw [hval, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) hinv

/-- **Kannan–Vempala Theorem 2, from a total-variation hypothesis.**

If the sampler's law `μ` is within total variation `ε` of the uniform law on `P' = S`, and
`ε · V ≤ θ` where `V = Vol(P')`, then for every lattice point `x`

  `(1 − (E + θ))/V  ≤  Pr[rnd p = x]  ≤  (1 + θ)/V`,

with `E` the escape mass — **exactly the shape `Arlib.KV97.theorem2` produces from its
pointwise hypothesis**, with `θ` in place of the pointwise `ε`.

This is what `AUDIT-KV97.md` §4b claims is impossible "at the required scale `1/Vol(P')`".
It is not impossible; it is a change of unit.  The cost is that the tolerance handed to the
mixing bound is `θ/V` rather than `θ`, i.e. `log V` extra steps
(`conductanceMixingTime_inv_volume_le`). -/
theorem theorem2_of_tvLe {S : Set (EuclideanSpace ℝ (Fin n))}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ] {V E θ : ℝ}
    {ε : ℝ≥0∞} {x : EuclideanSpace ℝ (Fin n)} (hS : MeasurableSet S)
    (h0 : volume S ≠ 0) (htop : volume S ≠ ⊤) (hVS : (volume S).toReal = V)
    (htv : TVLe μ (uniformOn volume S) ε) (hεtop : ε ≠ ⊤) (hεV : ε.toReal * V ≤ θ)
    (hesc : ∫ p in Sᶜ, prodTent x p ≤ E) :
    (1 - (E + θ)) / V ≤ ∫ p, prodTent x p ∂μ ∧
      ∫ p, prodTent x p ∂μ ≤ (1 + θ) / V := by
  haveI : IsProbabilityMeasure (uniformOn volume S) :=
    isProbabilityMeasure_uniformOn volume h0 htop
  have hV : 0 < V := hVS ▸ ENNReal.toReal_pos h0 htop
  obtain ⟨href1, href2⟩ := uniformOn_window hS hVS hV hesc
  obtain ⟨h1, h2⟩ := window_of_tvLe htv hεtop (measurable_prodTent x)
    (fun p => prodTent_nonneg x p) (fun p => prodTent_le_one x p) hV hεV href1 href2
  exact ⟨h1, by simpa using h2⟩

/-- **The same, with the tolerance written as `θ / V`.**  This is the form to run a mixing
bound to: *ask for total variation `θ / Vol(P')`*. -/
theorem theorem2_of_tvLe_inv_volume {S : Set (EuclideanSpace ℝ (Fin n))}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ] {V E θ : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hS : MeasurableSet S)
    (h0 : volume S ≠ 0) (htop : volume S ≠ ⊤) (hVS : (volume S).toReal = V)
    (htv : TVLe μ (uniformOn volume S) (ENNReal.ofReal (θ / V))) (hθ : 0 ≤ θ)
    (hesc : ∫ p in Sᶜ, prodTent x p ≤ E) :
    (1 - (E + θ)) / V ≤ ∫ p, prodTent x p ∂μ ∧
      ∫ p, prodTent x p ∂μ ≤ (1 + θ) / V := by
  have hV : 0 < V := hVS ▸ ENNReal.toReal_pos h0 htop
  refine theorem2_of_tvLe hS h0 htop hVS htv ENNReal.ofReal_ne_top ?_ hesc
  rw [ENNReal.toReal_ofReal (by positivity), div_mul_cancel₀ _ hV.ne']

/-- **End to end.**  A chain that has mixed, *in total variation*, to tolerance `θ / Vol(P')`
satisfies Kannan–Vempala Theorem 2's conclusion.  No pointwise hypothesis, no minorisation,
no density: `Arlib.MarkovChains.MixesWithin` is exactly what a conductance bound delivers,
and this is it being consumed. -/
theorem theorem2_of_mixesWithin {S : Set (EuclideanSpace ℝ (Fin n))}
    {P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))} [IsMarkovKernel P]
    {μ₀ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ₀] {V E θ : ℝ}
    {t : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hS : MeasurableSet S)
    (h0 : volume S ≠ 0) (htop : volume S ≠ ⊤) (hVS : (volume S).toReal = V) (hθ : 0 ≤ θ)
    (hmix : Arlib.MarkovChains.MixesWithin P (uniformOn volume S) μ₀ t
      (ENNReal.ofReal (θ / V)))
    (hesc : ∫ p in Sᶜ, prodTent x p ≤ E) :
    (1 - (E + θ)) / V ≤ ∫ p, prodTent x p ∂(Arlib.MarkovChains.iterate P μ₀ t) ∧
      ∫ p, prodTent x p ∂(Arlib.MarkovChains.iterate P μ₀ t) ≤ (1 + θ) / V :=
  theorem2_of_tvLe_inv_volume hS h0 htop hVS hmix hθ hesc

end KV97

/-! ## The price of the tolerance `θ / V`: `log V` extra steps

This is the quantitative half of the refutation of `AUDIT-KV97.md` §4b.  §4b writes off the
additive reading because `ε ≪ 1/Vol(P')` is required and "no sampler delivers" it.  But
mixing time is *logarithmic* in the tolerance: `Arlib.MarkovChains.conductanceMixingTime_le`
gives `O(φ⁻² log(M/ε))` steps, so replacing `ε` by `θ/V` costs an **additive**
`2·log V / φ²`.

For the Kannan–Vempala application `V = Vol(P')` is the volume of a `10^ρ`-dilated
polytope, so `log V = O(n·(ρ + log R))` — polynomial in the input size.  The entire
TV → pointwise gap therefore costs one factor of `O(n · bits)` in the step count. -/

/-- `log(1/(θ/V)) = log V + log(1/θ)`: the tolerance's contribution splits into the
volume's and the accuracy's. -/
theorem log_one_div_div {V θ : ℝ} (hV : 0 < V) (hθ : 0 < θ) :
    Real.log (1 / (θ / V)) = Real.log V + Real.log (1 / θ) := by
  have h : (1 : ℝ) / (θ / V) = V / θ := by field_simp
  rw [h, Real.log_div hV.ne' hθ.ne', one_div, Real.log_inv]
  ring

/-- **The cost, explicitly.**  Mixing to total variation `θ / V` takes at most

  `(log M + 2·log V + 2·log(1/θ)) / φ² + 1`

steps.  The dependence on the volume is `log V`, **not** `V`: this is why demanding a
tolerance at scale `1/Vol(P')` is affordable, and it is the fact `AUDIT-KV97.md` §4b
overlooks. -/
theorem conductanceMixingTime_inv_volume_le {M phi V θ : ℝ} (hM : 1 ≤ M) (hphi0 : 0 < phi)
    (hV : 0 < V) (hθ : 0 < θ) (hle : θ / V ≤ Real.sqrt M) :
    (Arlib.MarkovChains.conductanceMixingTime M phi (θ / V) : ℝ)
      ≤ (Real.log M + 2 * Real.log V + 2 * Real.log (1 / θ)) / phi ^ 2 + 1 := by
  have h := Arlib.MarkovChains.conductanceMixingTime_le hM hphi0 (by positivity) hle
  refine h.trans_eq ?_
  rw [log_one_div_div hV hθ]
  ring_nf

/-! ## Why the pointwise hypothesis is not merely hard but unattainable for a local walk

`Arlib.MarkovChains.PointwiseClose` and `Arlib.KV97.PointwiseAlmostUniform` both require the
sampler's law to *have a density*.  A ball walk started at a point never does: the holding
term `(1 − ℓ(x)) · δ_x` of `Arlib.MarkovChains.ballWalk_apply_set` leaves an atom of mass
`∏(1 − ℓ)` at the start, at **every** finite time.  One atom is fatal — not "costly", fatal:
absolute continuity fails, so the pointwise predicate is false for every `ε`, `⊤` included.

A total-variation hypothesis has no such defect: `exists_tvLe_with_atom` exhibits, for every
tolerance `δ ≠ 0`, a law with an atom of mass exactly `δ` that is nevertheless within `δ` of
the target in total variation.  Route 3 consumes such laws; routes 1 and 2 cannot. -/

/-- **One atom destroys pointwise closeness, for every `ε`.**  If `ν` gives `{x₀}` no mass
and `μ` gives it some, then `μ` is not absolutely continuous with respect to `ν`, and
`Arlib.MarkovChains.PointwiseClose μ ν ε` fails for every `ε` — `ε = ⊤` included. -/
theorem not_pointwiseClose_of_atom {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    {x₀ : Ω} (hν : ν {x₀} = 0) (hμ : μ {x₀} ≠ 0) (ε : ℝ≥0∞) :
    ¬ Arlib.MarkovChains.PointwiseClose μ ν ε := fun h => hμ (h.1 hν)

/-- A singleton that the ambient measure ignores is ignored by the uniform law too. -/
theorem uniformOn_singleton_eq_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Set Ω) {x₀ : Ω} (hx : μ {x₀} = 0) : uniformOn μ S {x₀} = 0 :=
  uniformOn_absolutelyContinuous μ S hx

/-- **The instance that matters.**  Against the uniform target on a body, a law with an atom
at a point of ambient measure zero — the law of a ball walk started at a point, at every
finite time — is not pointwise `ε`-close for any `ε`.  Contrast `exists_tvLe_with_atom`. -/
theorem not_pointwiseClose_uniformOn_of_atom {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} {S : Set Ω} {x₀ : Ω} (hx : ν {x₀} = 0) (hatom : μ {x₀} ≠ 0)
    (ε : ℝ≥0∞) : ¬ Arlib.MarkovChains.PointwiseClose μ (uniformOn ν S) ε :=
  not_pointwiseClose_of_atom (uniformOn_singleton_eq_zero ν S hx) hatom ε

/-- **A total-variation bound tolerates atoms.**  For every `δ ≠ 0` the law
`(1 − δ)·ν + δ·δ_{x₀}` is a probability measure within total variation `δ` of `ν`, yet has
an atom of mass `δ` at a `ν`-null point, so it is not pointwise `ε`-close to `ν` for any
`ε`.

Together with `Arlib.MarkovChains.not_exists_pointwiseClose_of_tvLe` this settles the
relationship between the two hypotheses: the pointwise one is not a strengthening a sampler
can be asked to pay more for, it is a hypothesis the sampler's law can *fail to be capable
of*, whereas the total-variation one is always available. -/
theorem exists_tvLe_with_atom {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {δ : ℝ≥0∞} (hδ0 : δ ≠ 0) (hδ1 : δ ≤ 1) {x₀ : Ω}
    (hx : ν {x₀} = 0) :
    ∃ μ : Measure Ω, IsProbabilityMeasure μ ∧ TVLe μ ν δ ∧
      ∀ ε : ℝ≥0∞, ¬ Arlib.MarkovChains.PointwiseClose μ ν ε := by
  refine ⟨(1 - δ) • ν + δ • Measure.dirac x₀, ?_, ?_, ?_⟩
  · constructor
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact tsub_add_cancel_of_le hδ1
  · intro S hS
    have hval : ((1 - δ) • ν + δ • Measure.dirac x₀) S
        = (1 - δ) * ν S + δ * Measure.dirac x₀ S := by
      simp [Measure.coe_add, Measure.coe_smul]
    have hd : Measure.dirac x₀ S ≤ 1 := prob_le_one
    have hsub : (1 - δ) * ν S = ν S - δ * ν S := by
      rw [ENNReal.sub_mul fun _ _ => measure_ne_top ν S, one_mul]
    refine ⟨?_, ?_⟩
    · rw [hval]
      calc (1 - δ) * ν S + δ * Measure.dirac x₀ S ≤ 1 * ν S + δ * 1 := by
            gcongr
            exact tsub_le_self
        _ = ν S + δ := by rw [one_mul, mul_one]
    · rw [hval, hsub]
      calc ν S ≤ ν S - δ * ν S + δ * ν S := le_tsub_add
        _ ≤ ν S - δ * ν S + δ := by
            gcongr
            calc δ * ν S ≤ δ * 1 := by gcongr; exact prob_le_one
              _ = δ := mul_one δ
        _ ≤ ν S - δ * ν S + δ * Measure.dirac x₀ S + δ := by
            rw [add_assoc]
            gcongr
            exact le_add_self
  · intro ε
    refine not_pointwiseClose_of_atom hx ?_ ε
    have hval : ((1 - δ) • ν + δ • Measure.dirac x₀) {x₀}
        = (1 - δ) * ν {x₀} + δ * Measure.dirac x₀ {x₀} := by
      simp [Measure.coe_add, Measure.coe_smul]
    rw [hval, hx, mul_zero, zero_add, Measure.dirac_apply_of_mem (mem_singleton x₀), mul_one]
    exact hδ0

/-! ## Route 2: rejection against an exactly-known proposal

Route 2 is *correct*, and it is the only route that delivers `ε = 0`.  If one can sample
exactly uniformly from a superset `B ⊇ S` — a box, a ball — then rejecting until the draw
lands in `S` gives a draw that is **exactly** uniform on `S`, so the pointwise hypothesis of
`Arlib.KV97.theorem2` holds at `ε = 0` and nothing has to be approximated at all.

This is what `Ttc/Witness/BoxProb.lean` does, and it is the non-vacuity witness for the
whole pointwise interface.  Its price is the acceptance probability `μ S / μ B`, computed
below, and the next section shows that price is superexponential for every pair that a
rounding transformation can produce. -/

section Rejection

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Rejection against an exactly-uniform proposal is exact.**

If `S ⊆ B` and `B` has positive finite measure, then conditioning a uniform draw from `B` on
landing in `S` gives *exactly* the uniform law on `S`:

  `condOn (uniformOn μ B) S = uniformOn μ S`.

No hypothesis on `μ S` is needed — at `μ S = 0` both sides are the zero measure, by the
`x / 0 = 0` conventions.  The acceptance probability is `uniformOn_acceptance`. -/
theorem condOn_uniformOn_eq_uniformOn (μ : Measure Ω) {B S : Set Ω} (hS : MeasurableSet S)
    (hSB : S ⊆ B) (hB0 : μ B ≠ 0) (hBtop : μ B ≠ ⊤) :
    condOn (uniformOn μ B) S = uniformOn μ S := by
  have hres : ((μ B)⁻¹ • μ.restrict B).restrict S = (μ B)⁻¹ • μ.restrict S := by
    rw [Measure.restrict_smul, Measure.restrict_restrict hS, Set.inter_eq_left.2 hSB]
  have hval : ((μ B)⁻¹ • μ.restrict B) S = (μ B)⁻¹ * μ S := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS, Set.inter_eq_left.2 hSB]
  have hscal : ((μ B)⁻¹ * μ S)⁻¹ * (μ B)⁻¹ = (μ S)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hBtop))
        (Or.inl (ENNReal.inv_ne_top.2 hB0)), inv_inv, mul_comm (μ B) ((μ S)⁻¹), mul_assoc,
      ENNReal.mul_inv_cancel hB0 hBtop, mul_one]
  rw [condOn_def, uniformOn_def μ B, uniformOn_def μ S, hval, hres, smul_smul, hscal]

/-- **The acceptance probability** of the rejection loop: a uniform draw from `B` lands in
`S` with probability `μ S / μ B`.  This is the entire cost of route 2, and the whole
question is whether it can be kept above `1/poly`. -/
theorem uniformOn_acceptance (μ : Measure Ω) {B S : Set Ω} (hB : MeasurableSet B)
    (hS : MeasurableSet S) (hSB : S ⊆ B) : uniformOn μ B S = μ S / μ B := by
  rw [uniformOn_apply μ hB hS, Set.inter_eq_left.2 hSB]

/-- **Rejection achieves pointwise error exactly `0`.**  The strongest form of the
hypothesis `Arlib.MarkovChains.PointwiseClose` — and the reason route 2 is worth stating
even though it is unaffordable. -/
theorem pointwiseClose_condOn_uniformOn (μ : Measure Ω) {B S : Set Ω} (hS : MeasurableSet S)
    (hSB : S ⊆ B) (hB0 : μ B ≠ 0) (hBtop : μ B ≠ ⊤) (hS0 : μ S ≠ 0) (hStop : μ S ≠ ⊤) :
    Arlib.MarkovChains.PointwiseClose (condOn (uniformOn μ B) S) (uniformOn μ S) 0 := by
  haveI : IsProbabilityMeasure (uniformOn μ S) := isProbabilityMeasure_uniformOn μ hS0 hStop
  rw [condOn_uniformOn_eq_uniformOn μ hS hSB hB0 hBtop]
  exact Arlib.MarkovChains.pointwiseClose_self _

/-- **The density form of the uniform law.**  `∫ g ∂(uniformOn μ S) = ∫_S (1/V)·g`, with
`V = (μ S).toReal`: the measure-form quantity of `theorem2_of_tvLe` and the density-form
quantity of `Arlib.KV97.theorem2` are the same number.  Unconditional, by
`Arlib.integral_uniformOn_real`. -/
theorem integral_uniformOn_eq_setIntegral_const_mul (μ : Measure Ω) (S : Set Ω) (g : Ω → ℝ) :
    ∫ x, g x ∂(uniformOn μ S) = ∫ x in S, (1 / (μ S).toReal) * g x ∂μ := by
  rw [integral_uniformOn_real, integral_const_mul, one_div]

end Rejection

/-- **Route 2 discharges `Arlib.KV97.theorem2`'s hypothesis outright.**

Rejecting a uniform draw from a superset `B ⊇ P'` onto `P'` gives a law under which
`Pr[rnd p = x]` is *literally* the density-form integrand of `Arlib.KV97.theorem2` at the
constant density `1/V`, and that density is `Arlib.KV97.PointwiseAlmostUniform` at error
`0` — hence at every `ε ≥ 0`.  Nothing is approximated.

So the pointwise interface is not vacuous and not unreachable; it is only *expensive*.  See
`uniformOn_ball_ball` for how expensive. -/
theorem pointwiseAlmostUniform_of_rejection {n : ℕ}
    {B S : Set (EuclideanSpace ℝ (Fin n))} {V ε : ℝ} (hS : MeasurableSet S) (hSB : S ⊆ B)
    (hB0 : volume B ≠ 0) (hBtop : volume B ≠ ⊤) (hVS : (volume S).toReal = V) (hV : 0 < V)
    (hε : 0 ≤ ε) (x : EuclideanSpace ℝ (Fin n)) :
    ∫ p, Arlib.Lattice.Rounding.prodTent x p ∂(condOn (uniformOn volume B) S)
        = ∫ p in S, (1 / V) * Arlib.Lattice.Rounding.prodTent x p ∧
      Arlib.KV97.PointwiseAlmostUniform (fun _ => 1 / V) S V ε := by
  refine ⟨?_, Arlib.KV97.PointwiseAlmostUniform.uniform S hV hε⟩
  rw [condOn_uniformOn_eq_uniformOn volume hS hSB hB0 hBtop,
    integral_uniformOn_eq_setIntegral_const_mul, hVS]

/-! ## Route 2's price: `(r/R)^n`, and no rounding transformation improves it

The acceptance probability is `Vol(S)/Vol(B)`, and the question the task poses is whether
the well-rounded / isotropic position that `lem:lattice` and `roundBody` put the body in
makes that only polynomially small.  It does not, and the computation is exact rather than
an estimate.

The best a rounding transformation guarantees is a sandwich `B(0,r) ⊆ K ⊆ B(0,R)` with
`R/r = O(√n)`.  Take the extreme case `K = B(0,r)`: `uniformOn_ball_ball` computes the
acceptance rate of rejecting from `B(0,R)` onto `B(0,r)` as **exactly** `(r/R)^n`.  At
`R/r = √n` that is `n^{−n/2}`, superexponentially small.  Since every `K` in the sandwich
has `Vol(K) ≤ Vol(B(0,R))`, the sandwich alone gives *no* lower bound on the acceptance rate
better than `(r/R)^n`, and that bound is attained.  **There is no polynomial regime.**

`Ttc/Witness/BoxProb.lean` escapes this only because its `P'` *is* the proposal box: there
`B = S` and the acceptance rate is `1`.  That is a witness, not an algorithm. -/

section BallPrice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The acceptance rate of ball-into-ball rejection is exactly `(r/R)^n`.**

`n = finrank ℝ E`.  The normalising constant `μ (ball 0 1)` — the only place a Gamma
function would appear — cancels, so this is an identity, not an estimate. -/
theorem uniformOn_ball_ball {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    uniformOn μ (Metric.ball 0 R) (Metric.ball 0 r)
      = ENNReal.ofReal ((r / R) ^ Module.finrank ℝ E) := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hc0 : μ (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos μ 0 one_pos).ne'
  have hctop : μ (Metric.ball (0 : E) 1) ≠ ⊤ := measure_ball_ne_top
  rw [uniformOn_apply μ measurableSet_ball measurableSet_ball,
    Set.inter_eq_left.2 (Metric.ball_subset_ball hrR),
    Measure.addHaar_ball_of_pos μ 0 hr, Measure.addHaar_ball_of_pos μ 0 hR,
    ENNReal.mul_div_mul_right _ _ hc0 hctop, ← ENNReal.ofReal_div_of_pos (by positivity),
    div_pow]

/-- **The well-rounded case.**  With the body normalised to contain the unit ball and be
contained in `B(0,R)`, rejection from the circumscribed ball accepts with probability
`(1/R)^n`.  At the best `R` a rounding transformation guarantees, `R = Θ(√n)`, this is
`n^{−n/2}`. -/
theorem uniformOn_ball_ball_one {R : ℝ} (hR : 1 ≤ R) :
    uniformOn μ (Metric.ball 0 R) (Metric.ball 0 1)
      = ENNReal.ofReal ((1 / R) ^ Module.finrank ℝ E) :=
  uniformOn_ball_ball μ one_pos hR

end BallPrice

/-- The same, on the space the sampler actually lives on, with the exponent displayed as
the dimension `n + 1`. -/
theorem uniformOn_ball_ball_euclidean {n : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    uniformOn (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
        (Metric.ball 0 R) (Metric.ball 0 r)
      = ENNReal.ofReal ((r / R) ^ (n + 1)) := by
  rw [uniformOn_ball_ball (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) hr hrR,
    finrank_euclideanSpace_fin]

/-! ## Non-vacuity (`CLAUDE.md` §11)

`theorem2_of_tvLe` is a conditional statement with seven hypotheses; if they could not hold
together it would be worthless.  They can, at the extreme value `ε = 0`: take the body to be
the unit ball of `EuclideanSpace ℝ (Fin (n+1))` (positive and finite volume) and the
sampler's law to be *exactly* the uniform law on it.  Then the total-variation hypothesis
holds at **every** tolerance, the tolerance `θ/V` included, and the conclusion is the
genuine two-sided window, not a degenerate one. -/

/-- **The non-vacuity witness.**  Every hypothesis of `theorem2_of_tvLe_inv_volume` is
simultaneously satisfiable, and the conclusion it yields there is the honest window
`[(1 − (E+θ))/V, (1+θ)/V]` about a body of positive finite volume. -/
theorem exists_theorem2_of_tvLe_witness (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (V E : ℝ),
      IsProbabilityMeasure μ ∧ MeasurableSet S ∧ volume S ≠ 0 ∧ volume S ≠ ⊤ ∧
        (volume S).toReal = V ∧ 0 < V ∧
        TVLe μ (uniformOn volume S) (ENNReal.ofReal (θ / V)) ∧
        (∫ p in Sᶜ, Arlib.Lattice.Rounding.prodTent x p) ≤ E ∧
        ((1 - (E + θ)) / V ≤ ∫ p, Arlib.Lattice.Rounding.prodTent x p ∂μ ∧
          (∫ p, Arlib.Lattice.Rounding.prodTent x p ∂μ) ≤ (1 + θ) / V) := by
  set S : Set (EuclideanSpace ℝ (Fin (n + 1))) := Metric.ball 0 1 with hSdef
  have hS : MeasurableSet S := measurableSet_ball
  have h0 : volume S ≠ 0 := (Metric.measure_ball_pos volume 0 one_pos).ne'
  have htop : volume S ≠ ⊤ := measure_ball_ne_top
  have hV : 0 < (volume S).toReal := ENNReal.toReal_pos h0 htop
  haveI : IsProbabilityMeasure (uniformOn volume S) :=
    isProbabilityMeasure_uniformOn volume h0 htop
  refine ⟨S, uniformOn volume S, (volume S).toReal,
    ∫ p in Sᶜ, Arlib.Lattice.Rounding.prodTent x p, inferInstance, hS, h0, htop, rfl, hV,
    (TVLe.refl _).mono (by simp), le_rfl, ?_⟩
  exact theorem2_of_tvLe_inv_volume hS h0 htop rfl ((TVLe.refl _).mono (by simp)) hθ le_rfl

/-! ## Axiom check (`CLAUDE.md` §4) -/

#print axioms window_of_tvLe
#print axioms window_of_tvLe_inv_volume
#print axioms ratio_bounds_of_tvLe
#print axioms prodTent_le_one
#print axioms uniformOn_window
#print axioms theorem2_of_tvLe
#print axioms theorem2_of_tvLe_inv_volume
#print axioms theorem2_of_mixesWithin
#print axioms conductanceMixingTime_inv_volume_le
#print axioms not_pointwiseClose_of_atom
#print axioms not_pointwiseClose_uniformOn_of_atom
#print axioms exists_tvLe_with_atom
#print axioms condOn_uniformOn_eq_uniformOn
#print axioms uniformOn_acceptance
#print axioms pointwiseClose_condOn_uniformOn
#print axioms pointwiseAlmostUniform_of_rejection
#print axioms uniformOn_ball_ball
#print axioms uniformOn_ball_ball_euclidean
#print axioms exists_theorem2_of_tvLe_witness

end Arlib.PointwiseRoute
