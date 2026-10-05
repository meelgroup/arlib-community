/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.ContTent
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.KV97.Inflate

/-!
# Kannan–Vempala, *Sampling Lattice Points*, Theorem 2

> Suppose `p` is picked from a distribution over `P' = {x : Ax ≤ b + κ‖A‖}` that
> is close to uniform. Then for every lattice point `x ∈ P ∩ ℤⁿ`,
> `(1 − loss)/Vol(P') ≤ Pr[rnd p = x] ≤ 1/Vol(P')`.

`Arlib.KV97.theorem2` is that statement. `Pr[rnd p = x]` is
`∫_{P'} f p · prodTent x p dp`, where `f` is the sampler's density and
`prodTent x p = ∏ᵢ tent(pᵢ − xᵢ)` is `Pr[rnd p = x ∣ p]`
(`Arlib/Lattice/Rounding/ProdKernel.lean`).

## The hypothesis is POINTWISE, not total-variation — and this is a correction

Both Kannan–Vempala and the restatement it is used through
(`sections/proof-appendix.tex:153`, `claim:linf`) say the sampler's density is
within **total variation** `ε` of uniform on `P'`. That reading does not survive
contact with the corollary, and this development does not use it. In detail
(`AUDIT-KV97.md` §4b):

* A TV hypothesis buys an **additive** error: the integrand `prodTent x ·` lies in
  `[0,1]`, so `|∫f dν − ∫f dunif| ≤ TV(ν, unif)` and no better. That is exactly
  what KV97's own proof derives — `Pr[rnd p = x] = (1/Vol(P'))·∫_{P'} … + c` with
  `|c| ≤ ε`.
* But the theorem is *stated* with `ε` inside the numerator, i.e. as a
  **relative** error. The two differ by a factor of `Vol(P')`, which is enormous.
* Under the additive reading the theorem is useless: `1/Vol(P')` is tiny, so an
  additive `ε` swamps it. And `cor:linf` divides by the acceptance probability
  and needs the `ε`s to cancel; summing an additive `ε` over the `N` lattice
  points contributes `N·ε`, which does not cancel.

So the hypothesis here is `(1−ε)/V ≤ f p ≤ (1+ε)/V` pointwise on `P'` — the
continuous analogue of `eq:almostuniform`. **This is a strengthening of what the
papers assume, and it is load-bearing.** Its cost is recorded honestly: the
continuous sampler that must eventually be built has to be almost-uniform
pointwise, not merely mixed in total variation, and upgrading one to the other is
a further argument that neither paper gives.

`Arlib.TVLe` (`Arlib/Probability/TV.lean`) remains the honest total-variation
object and `TVLe.integral_le` the honest additive transfer; they are simply not
what this theorem consumes.

## The upper bound is `(1+ε)/V`, not `1/V`

A second, smaller deviation. With a pointwise `(1±ε)` density the upper bound is
`(1+ε)/Vol(P')`; the papers' `1/Vol(P')` would need `f ≤ 1/V`, i.e. a density
never exceeding uniform, which is not what "almost uniform" says. The asymmetry
costs nothing downstream: `Arlib.Rejection.ratio_bounds_of_window` is stated for
exactly this two-sided window `[(1−a)/V, (1+b)/V]`.

## What is assumed and what is proved

The escape mass `∫_{P'ᶜ} prodTent x p dp` enters as an explicit real `E` with a
hypothesis bounding it. That is deliberate: the two halves of Theorem 2 —
the *averaging* against the sampler's density (here) and the *tail bound* on the
escape (`Arlib/Lattice/KV97/Escape.lean`, `Arlib/Lattice/Rounding/ContTent.lean`)
— are independent, and keeping them separate makes each checkable on its own.

`Arlib.KV97.theorem2` is conditional on `E`. **`Arlib.KV97.theorem2_of_body`
below is not**: it discharges `E` at `exp(−c²/2)` using
`Arlib.Lattice.Rounding.setIntegral_prodTent_compl_inflate_le_exp`, which
transports the facet tail bound of `Escape.lean` to the *continuous* tent density
that Theorem 2's escape term is actually under. That is the form to read as
"Kannan–Vempala Theorem 2".
-/

namespace Arlib.KV97

open MeasureTheory Arlib.Lattice.Rounding

variable {n : ℕ} {ι : Type*}

/-- **The sampler's density is pointwise almost uniform on `S`.**

The continuous analogue of `eq:almostuniform` (`sections/related.tex:21`): `f` is
a density on `S` whose value at every point is within a `(1±ε)` factor of the
uniform density `1/V`. See the module docstring for why this, and not a
total-variation bound, is the right hypothesis. -/
def PointwiseAlmostUniform (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) (V ε : ℝ) : Prop :=
  ∀ p ∈ S, (1 - ε) / V ≤ f p ∧ f p ≤ (1 + ε) / V

namespace PointwiseAlmostUniform

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : Set (EuclideanSpace ℝ (Fin n))}
  {V ε : ℝ}

theorem lower (h : PointwiseAlmostUniform f S V ε) {p} (hp : p ∈ S) :
    (1 - ε) / V ≤ f p := (h p hp).1

theorem upper (h : PointwiseAlmostUniform f S V ε) {p} (hp : p ∈ S) :
    f p ≤ (1 + ε) / V := (h p hp).2

/-- **Non-vacuity** (`CLAUDE.md` §11): the exactly-uniform density satisfies it for
every `ε ≥ 0`, so the hypothesis is not empty. -/
theorem uniform (S : Set (EuclideanSpace ℝ (Fin n))) {V ε : ℝ} (hV : 0 < V)
    (hε : 0 ≤ ε) : PointwiseAlmostUniform (fun _ => 1 / V) S V ε := by
  intro p _
  have hinv : (0:ℝ) ≤ V⁻¹ := inv_nonneg.mpr hV.le
  constructor
  · have h : (1 - ε) * V⁻¹ ≤ 1 * V⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) hinv
    simpa [div_eq_mul_inv] using h
  · have h : (1:ℝ) * V⁻¹ ≤ (1 + ε) * V⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) hinv
    simpa [div_eq_mul_inv] using h

end PointwiseAlmostUniform

/-! ## The two halves -/

/-- **Theorem 2, upper bound.** `Pr[rnd p = x] ≤ (1+ε)/V`.

The whole content is double stochasticity: the kernel integrates to `1` in the
`p` variable (`Arlib.Lattice.Rounding.integral_prodTent`), hence to at most `1`
over any measurable set. -/
theorem theorem2_upper {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {V ε : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hS : MeasurableSet S) (hV : 0 < V) (hε : -1 ≤ ε)
    (hf : PointwiseAlmostUniform f S V ε)
    (hint : IntegrableOn (fun p => f p * prodTent x p) S) :
    ∫ p in S, f p * prodTent x p ≤ (1 + ε) / V := by
  have hcoef : 0 ≤ (1 + ε) / V := div_nonneg (by linarith) hV.le
  calc ∫ p in S, f p * prodTent x p
      ≤ ∫ p in S, ((1 + ε) / V) * prodTent x p := by
        refine setIntegral_mono_on hint (((integrableOn_prodTent x S).const_mul _)) hS ?_
        intro p hp
        exact mul_le_mul_of_nonneg_right (hf.upper hp) (prodTent_nonneg x p)
    _ = ((1 + ε) / V) * ∫ p in S, prodTent x p := integral_const_mul _ _
    _ ≤ ((1 + ε) / V) * 1 :=
        mul_le_mul_of_nonneg_left (setIntegral_prodTent_le_one x hS) hcoef
    _ = (1 + ε) / V := mul_one _

/-- **Theorem 2, lower bound.** `Pr[rnd p = x] ≥ (1−ε)(1−E)/V`, where `E` bounds
the escape mass `∫_{Sᶜ} prodTent x p dp`.

The kernel's total mass is `1`, so what stays inside `S` is `1` minus what
escapes (`Arlib.Lattice.Rounding.setIntegral_prodTent_compl`); the sampler's
density is at least `(1−ε)/V` there. -/
theorem theorem2_lower {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {V ε E : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hS : MeasurableSet S) (hV : 0 < V) (hε : ε ≤ 1)
    (hf : PointwiseAlmostUniform f S V ε)
    (hint : IntegrableOn (fun p => f p * prodTent x p) S)
    (hesc : ∫ p in Sᶜ, prodTent x p ≤ E) :
    (1 - ε) * (1 - E) / V ≤ ∫ p in S, f p * prodTent x p := by
  have hcoef : 0 ≤ (1 - ε) / V := div_nonneg (by linarith) hV.le
  have hinside : 1 - E ≤ ∫ p in S, prodTent x p := by
    rw [setIntegral_prodTent_compl x hS]; linarith
  calc (1 - ε) * (1 - E) / V = ((1 - ε) / V) * (1 - E) := by ring
    _ ≤ ((1 - ε) / V) * ∫ p in S, prodTent x p :=
        mul_le_mul_of_nonneg_left hinside hcoef
    _ = ∫ p in S, ((1 - ε) / V) * prodTent x p := (integral_const_mul _ _).symm
    _ ≤ ∫ p in S, f p * prodTent x p := by
        refine setIntegral_mono_on (((integrableOn_prodTent x S).const_mul _)) hint hS ?_
        intro p hp
        exact mul_le_mul_of_nonneg_right (hf.lower hp) (prodTent_nonneg x p)

/-- **Kannan–Vempala, Theorem 2.**

For a sampler whose density on the inflated polytope `P'` is pointwise within a
`(1±ε)` factor of uniform, and with escape mass at most `E`, the probability that
the randomized rounding of a draw equals a given lattice point `x` satisfies

`(1−ε)(1−E)/V  ≤  Pr[rnd p = x]  ≤  (1+ε)/V`,   `V = Vol(P')`.

Read the module docstring for the two deviations from the printed statement: the
hypothesis is pointwise rather than total-variation, and the upper bound carries
a `(1+ε)`. Both are corrections, not conveniences.

`E` is discharged by the tail bound of `Arlib/Lattice/KV97/Escape.lean`
transported to the continuous tent density; at `κ = kappaOf c r` that gives
`E = exp(−c²/2)` (**not** `exp(−c²)` — `AUDIT-KV97.md` §4a). -/
theorem theorem2 {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ} {c r : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {V ε E : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hV : 0 < V) (hε0 : -1 ≤ ε) (hε1 : ε ≤ 1)
    (hf : PointwiseAlmostUniform f (inflated A b c r) V ε)
    (hint : IntegrableOn (fun p => f p * prodTent x p) (inflated A b c r))
    (hesc : ∫ p in (inflated A b c r)ᶜ, prodTent x p ≤ E) :
    (1 - ε) * (1 - E) / V ≤ ∫ p in inflated A b c r, f p * prodTent x p ∧
      ∫ p in inflated A b c r, f p * prodTent x p ≤ (1 + ε) / V :=
  ⟨theorem2_lower (measurableSet_inflated A b c r) hV hε1 hf hint hesc,
   theorem2_upper (measurableSet_inflated A b c r) hV hε0 hf hint⟩


/-! ## The unconditional form

`Arlib.KV97.theorem2` leaves the escape mass `E` as a hypothesis. Everything
needed to discharge it is now proved, so this section closes it.
-/

/-- **Kannan–Vempala Theorem 2, unconditional.**

For a lattice point `x` of the *un-inflated* polytope `P = {z : Az ≤ b}`, and a
sampler whose density on `P' = inflated A b c r` is pointwise within a `(1±ε)`
factor of uniform,

`(1−ε)(1 − e^{−c²/2})/V  ≤  Pr[rnd p = x]  ≤  (1+ε)/V`,   `V = Vol(P')`.

The escape term is `exp(−c²/2)` — **not** the paper's `2e^{−c²}`. The paper's
inflation `κ = c + √(2 log r)` supports only the former; see `AUDIT-KV97.md` §4a
and `Arlib.KV97.mul_exp_kappaOf_le`. Reaching `e^{−c²}` needs the larger
inflation `√2·c + √(2 log r)`, available as
`Arlib.KV97.mul_exp_kappaOf_sqrt_two_le`.

Both the escape bound and the union bound over facets are discharged here; the
only remaining hypotheses are about the *sampler* (`hf`, `hint`) and the input
geometry (`hx`, `hr`). -/
theorem theorem2_of_body [Fintype ι] {A : ι → EuclideanSpace ℝ (Fin n)} {b : ι → ℝ}
    {c r : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {V ε : ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hV : 0 < V) (hε0 : -1 ≤ ε) (hε1 : ε ≤ 1)
    (hf : PointwiseAlmostUniform f (inflated A b c r) V ε)
    (hint : IntegrableOn (fun p => f p * prodTent x p) (inflated A b c r))
    (hx : x ∈ Arlib.Polytope.body A b) (hc : 0 ≤ c) (hr1 : 1 ≤ r)
    (hr : (Fintype.card ι : ℝ) ≤ r) :
    (1 - ε) * (1 - Real.exp (-c ^ 2 / 2)) / V
        ≤ ∫ p in inflated A b c r, f p * prodTent x p ∧
      ∫ p in inflated A b c r, f p * prodTent x p ≤ (1 + ε) / V :=
  theorem2 hV hε0 hε1 hf hint
    (setIntegral_prodTent_compl_inflate_le_exp A b hx hc hr1 hr)

end Arlib.KV97
