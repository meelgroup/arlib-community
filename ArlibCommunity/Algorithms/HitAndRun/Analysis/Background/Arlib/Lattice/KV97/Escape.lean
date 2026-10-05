/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Convexity.Polytope
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Probability.SubgaussianTail
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.KV97.Defs
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.RoundLaw

/-!
# Kannan–Vempala Theorem 2: the rounded point rarely escapes the inflated body

This is the lower-bound core of Kannan–Vempala's Theorem 2. Let
`P = Arlib.Polytope.body A b` be a polytope, `x ∈ P`, and let `Z` be a random
displacement whose coordinates are independent, supported in `[-1,1]` and mean
zero — exactly what a coordinatewise randomized rounding produces
(`Arlib.Lattice.Rounding.roundLaw`). Then

  `Pr[ x + Z ∉ inflate A b κ ] ≤ r · exp(-κ²/2)`,

where `r` bounds the number of facets.
-/

namespace Arlib.KV97

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

/-! ## Bridging `EuclideanSpace ℝ (Fin n)` and `Fin n → ℝ`

`Arlib.Polytope.body` lives on `EuclideanSpace ℝ (Fin n)` and speaks of `⟪·,·⟫_ℝ`
and `‖·‖`; `Arlib.Probability.rounding_tail_bound` lives on `Fin n → ℝ` and speaks
of `∑ k, A k * Y k` and `Arlib.Probability.coeffNorm`. These two lemmas are the
whole of the translation, and are used nowhere else than in
`Arlib.KV97.facet_escape_prob_le`. -/

/-- The Euclidean norm of a vector is the `Arlib.Probability.coeffNorm` of its
coordinate function. -/
theorem coeffNorm_coords {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    Arlib.Probability.coeffNorm (fun k => v k) = ‖v‖ := by
  rw [Arlib.Probability.coeffNorm, EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt (Finset.sum_congr rfl fun k _ => by
    rw [Real.norm_eq_abs, sq_abs])

/-- The real inner product on `EuclideanSpace ℝ (Fin n)` is the coordinate sum. -/
theorem inner_eq_sum_coords {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪v, w⟫_ℝ = ∑ k, v k * w k := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [RCLike.inner_apply (𝕜 := ℝ) (v k) (w k), starRingEnd_apply, star_trivial, mul_comm]

/-! ## Step 1: the escape event is a union over facets -/

/-- **The escape is covered by the facet-crossing events.**

If `x` lies in the polytope `body A b` and `x + z` escapes its `κ`-inflation,
then some facet `i` is crossed by the displacement alone:
`κ‖A i‖ < ⟪A i, z⟫`. Indeed `⟪A i, x⟫ ≤ b i` and
`b i + κ‖A i‖ < ⟪A i, x⟫ + ⟪A i, z⟫`.

The inequality obtained is **strict**, which matters: for a degenerate facet
`A i = 0` it makes the crossing event empty rather than everything, so no
nondegeneracy hypothesis is needed anywhere downstream. -/
theorem exists_facet_crossed {n : ℕ} {ι : Type*} {A : ι → EuclideanSpace ℝ (Fin n)}
    {b : ι → ℝ} {κ : ℝ} {x z : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    (hz : x + z ∉ Polytope.inflate A b κ) :
    ∃ i, κ * ‖A i‖ < ⟪A i, z⟫_ℝ := by
  simp only [Polytope.inflate, Set.mem_setOf_eq, not_forall, not_le] at hz
  obtain ⟨i, hi⟩ := hz
  refine ⟨i, ?_⟩
  rw [inner_add_right] at hi
  have := hx i
  linarith

/-- **Step 1: the escape event is contained in the union of the facet-crossing
events.** Pure set logic on top of `Arlib.KV97.exists_facet_crossed`. -/
theorem escape_subset_iUnion {n : ℕ} {ι Ω : Type*} (A : ι → EuclideanSpace ℝ (Fin n))
    (b : ι → ℝ) (κ : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    (Z : Ω → EuclideanSpace ℝ (Fin n)) :
    {ω | x + Z ω ∉ Polytope.inflate A b κ}
      ⊆ ⋃ i, {ω | κ * ‖A i‖ < ⟪A i, Z ω⟫_ℝ} := by
  intro ω hω
  obtain ⟨i, hi⟩ := exists_facet_crossed hx hω
  exact Set.mem_iUnion.2 ⟨i, hi⟩

/-! ## Step 2: each facet-crossing event is exponentially unlikely -/

section Facet

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Step 2: the sub-Gaussian bound for a single facet.**

If the coordinates of `Z` are independent, supported in `[-1,1]` and mean zero,
then for every coefficient vector `a` and every `κ ≥ 0`,

  `Pr[ κ‖a‖ < ⟪a, Z⟫ ] ≤ exp(-κ²/2)`.

This is `Arlib.Probability.rounding_tail_bound` transported along
`Arlib.KV97.coeffNorm_coords` and `Arlib.KV97.inner_eq_sum_coords`. The
degenerate case `a = 0` — excluded by `rounding_tail_bound`'s hypothesis
`0 < ∑ k, a k ^ 2` — is handled separately: the event is then empty, because the
inequality is strict. -/
theorem facet_escape_prob_le (Z : Ω → EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n))
    (hmeas : ∀ k, AEMeasurable (fun ω => Z ω k) μ)
    (hindep : iIndepFun (fun k ω => a k * Z ω k) μ)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, Z ω k ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ k, μ[fun ω => Z ω k] = 0)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    μ.real {ω | κ * ‖a‖ < ⟪a, Z ω⟫_ℝ} ≤ Real.exp (-κ ^ 2 / 2) := by
  rcases eq_or_ne a 0 with rfl | ha
  · -- degenerate facet: the strict inequality `0 < 0` is unsatisfiable
    have hempty : {ω | κ * ‖(0 : EuclideanSpace ℝ (Fin n))‖ < ⟪(0 : EuclideanSpace ℝ (Fin n)),
        Z ω⟫_ℝ} = (∅ : Set Ω) := by
      ext ω
      simp
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le
  · have hpos : 0 < ∑ k, (a k) ^ 2 := by
      have hnorm : 0 < ‖a‖ := norm_pos_iff.2 ha
      have := EuclideanSpace.real_norm_sq_eq a
      nlinarith
    have hsub : {ω | κ * ‖a‖ < ⟪a, Z ω⟫_ℝ}
        ⊆ {ω | κ * Arlib.Probability.coeffNorm (fun k => a k) ≤ ∑ k, a k * Z ω k} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [coeffNorm_coords, ← inner_eq_sum_coords]
      exact hω.le
    refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
    exact Arlib.Probability.rounding_tail_bound (fun k ω => Z ω k) (fun k => a k)
      hmeas hindep hbdd hmean hκ hpos

end Facet

/-! ## Steps 3 and 4: the union bound and the headline estimate -/

section Escape

variable {n : ℕ} {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- **Step 3: the union bound over facets.** If each of `Fintype.card ι` events
has probability at most `t ≥ 0`, and `r` bounds the number of facets, their union
has probability at most `r · t`. -/
theorem measureReal_iUnion_le_card_mul {S : ι → Set Ω} {t r : ℝ} (ht : 0 ≤ t)
    (hS : ∀ i, μ.real (S i) ≤ t) (hr : (Fintype.card ι : ℝ) ≤ r) :
    μ.real (⋃ i, S i) ≤ r * t := by
  refine le_trans (measureReal_iUnion_fintype_le (μ := μ) S) ?_
  calc ∑ _i : ι, μ.real (S _i) ≤ ∑ _i : ι, t := Finset.sum_le_sum fun i _ => hS i
    _ = (Fintype.card ι : ℝ) * t := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ r * t := mul_le_mul_of_nonneg_right hr ht

/-- **Step 4: Kannan–Vempala Theorem 2, the escape estimate.**

Let `x` be a point of the polytope `body A b`, and let `Z` be a random
displacement whose coordinates are independent, supported in `[-1,1]` and mean
zero. Then

  `Pr[ x + Z ∉ inflate A b κ ] ≤ r · exp(-κ²/2)`

for every `κ ≥ 0` and every `r` bounding the number of facets.

Note that `hindep` is required for every facet separately, because
`Arlib.Probability.rounding_tail_bound` consumes independence of the *scaled*
coordinates `A i k · Z k`; for a product law such as
`Arlib.Lattice.Rounding.roundLaw` this is uniform in `A` (see
`Arlib.KV97.roundLaw_escape_prob_le`). -/
theorem escape_prob_le (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    (Z : Ω → EuclideanSpace ℝ (Fin n))
    (hmeas : ∀ k, AEMeasurable (fun ω => Z ω k) μ)
    (hindep : ∀ i, iIndepFun (fun k ω => A i k * Z ω k) μ)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, Z ω k ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ k, μ[fun ω => Z ω k] = 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    {κ r : ℝ} (hκ : 0 ≤ κ) (hr : (Fintype.card ι : ℝ) ≤ r) :
    μ.real {ω | x + Z ω ∉ Polytope.inflate A b κ} ≤ r * Real.exp (-κ ^ 2 / 2) := by
  refine le_trans (measureReal_mono (escape_subset_iUnion A b κ hx Z) (measure_ne_top _ _)) ?_
  exact measureReal_iUnion_le_card_mul (Real.exp_pos _).le
    (fun i => facet_escape_prob_le Z (A i) hmeas (hindep i) hbdd hmean hκ) hr

end Escape

/-! ## Step 5: the corollary at `κ = kappaOf c r`

### The constant that actually comes out

`Arlib.KV97.kappaOf c r = c + √(2 log r)`. With `a, b ≥ 0` one has
`(a + b)² ≥ a² + b²`, so `kappaOf c r ^ 2 ≥ c² + 2 log r` and therefore

  `r · exp(-(kappaOf c r)²/2) ≤ r · exp(-c²/2) · exp(-log r) = exp(-c²/2)`.

The honest constant is thus **`exp(-c²/2)`, not `exp(-c²)`**. This is a genuine
discrepancy with `Arlib.KV97.lossOf c ε = 2·exp(-c²) + ε`, whose exponential half
budgets `exp(-c²)` per escape event. Nothing here is weakened to hide it: to
obtain `exp(-c²)` from this argument one must inflate by `√2·c + √(2 log r)`
rather than `c + √(2 log r)` — i.e. `lossOf`'s `c` is this file's `c/√2`. -/

section Kappa

/-- **The arithmetic of step 5.** For `0 ≤ c` and `1 ≤ r`,
`r · exp(-(kappaOf c r)²/2) ≤ exp(-c²/2)`: the `√(2 log r)` summand in `kappaOf`
is exactly what absorbs the factor `r` produced by the union bound. -/
theorem mul_exp_kappaOf_le {c r : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r) :
    r * Real.exp (-(kappaOf c r) ^ 2 / 2) ≤ Real.exp (-c ^ 2 / 2) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hlog : 0 ≤ Real.log r := Real.log_nonneg hr
  have hs : 0 ≤ Real.sqrt (2 * Real.log r) := Real.sqrt_nonneg _
  have hsq : c ^ 2 + 2 * Real.log r ≤ (kappaOf c r) ^ 2 := by
    rw [kappaOf, add_sq, Real.sq_sqrt (by linarith)]
    nlinarith
  have hle : -(kappaOf c r) ^ 2 / 2 ≤ -c ^ 2 / 2 - Real.log r := by linarith
  calc r * Real.exp (-(kappaOf c r) ^ 2 / 2)
      ≤ r * Real.exp (-c ^ 2 / 2 - Real.log r) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hr0.le
    _ = Real.exp (-c ^ 2 / 2) := by
        rw [Real.exp_sub, Real.exp_log hr0]
        field_simp

/-- **The rate `Arlib.KV97.lossOf` budgets, at the price of a larger inflation.**
Inflating by `kappaOf (√2·c) r = √2·c + √(2 log r)` — rather than by
`kappaOf c r` — does give `exp(-c²)`, the exponential half of
`Arlib.KV97.lossOf c ε`. This is `Arlib.KV97.mul_exp_kappaOf_le` at `√2·c`,
recorded to make the size of the discrepancy explicit. -/
theorem mul_exp_kappaOf_sqrt_two_le {c r : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r) :
    r * Real.exp (-(kappaOf (Real.sqrt 2 * c) r) ^ 2 / 2) ≤ Real.exp (-c ^ 2) := by
  refine le_trans (mul_exp_kappaOf_le (by positivity) hr) (le_of_eq ?_)
  congr 1
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

variable {n : ℕ} {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **Step 5: the escape bound at `κ = kappaOf c r`.**

Inflating by `kappaOf c r = c + √(2 log r)` makes the escape probability at most
`exp(-c²/2)`, with the factor `r` from the union bound absorbed.

**The constant is `exp(-c²/2)`, not the `exp(-c²)` budgeted by
`Arlib.KV97.lossOf`.** See the section docstring above. -/
theorem escape_prob_le_exp (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    (Z : Ω → EuclideanSpace ℝ (Fin n))
    (hmeas : ∀ k, AEMeasurable (fun ω => Z ω k) μ)
    (hindep : ∀ i, iIndepFun (fun k ω => A i k * Z ω k) μ)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, Z ω k ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ k, μ[fun ω => Z ω k] = 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    {c r : ℝ} (hc : 0 ≤ c) (hr1 : 1 ≤ r) (hr : (Fintype.card ι : ℝ) ≤ r) :
    μ.real {ω | x + Z ω ∉ Polytope.inflate A b (kappaOf c r)} ≤ Real.exp (-c ^ 2 / 2) :=
  le_trans
    (escape_prob_le A b Z hmeas hindep hbdd hmean hx (kappaOf_nonneg hc) hr)
    (mul_exp_kappaOf_le hc hr1)

/-- **The escape bound at the inflation that meets `Arlib.KV97.lossOf`'s budget.**
Inflating by `kappaOf (√2·c) r` makes the escape probability at most `exp(-c²)`,
matching the exponential half of `Arlib.KV97.lossOf c ε`. Compare
`Arlib.KV97.escape_prob_le_exp`, which uses the smaller inflation `kappaOf c r`
and only reaches `exp(-c²/2)`. -/
theorem escape_prob_le_exp_sq (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    (Z : Ω → EuclideanSpace ℝ (Fin n))
    (hmeas : ∀ k, AEMeasurable (fun ω => Z ω k) μ)
    (hindep : ∀ i, iIndepFun (fun k ω => A i k * Z ω k) μ)
    (hbdd : ∀ k, ∀ᵐ ω ∂μ, Z ω k ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ k, μ[fun ω => Z ω k] = 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    {c r : ℝ} (hc : 0 ≤ c) (hr1 : 1 ≤ r) (hr : (Fintype.card ι : ℝ) ≤ r) :
    μ.real {ω | x + Z ω ∉ Polytope.inflate A b (kappaOf (Real.sqrt 2 * c) r)}
      ≤ Real.exp (-c ^ 2) :=
  le_trans
    (escape_prob_le A b Z hmeas hindep hbdd hmean hx
      (kappaOf_nonneg (by positivity)) hr)
    (mul_exp_kappaOf_sqrt_two_le hc hr1)

end Kappa

/-! ## The instance: randomized rounding on `ℤⁿ`

`Arlib.Lattice.Rounding.roundLaw p` is the law of the coordinatewise randomized
rounding of `p`, and `p − z` is the displacement it produces. It discharges every
hypothesis of `Arlib.KV97.escape_prob_le`. -/

section RoundLaw

open Arlib.Lattice.Rounding

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The rounding displacement `p − z` read as a vector of `EuclideanSpace ℝ (Fin n)`,
so that it can be added to a point of a `Arlib.Polytope.body`. -/
noncomputable def latDispVec (p : Fin n → ℝ) (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => p k - (z k : ℝ))

@[simp]
theorem latDispVec_apply (p : Fin n → ℝ) (z : Fin n → ℤ) (k : Fin n) :
    latDispVec p z k = p k - (z k : ℝ) := rfl

/-- **The escape bound for randomized rounding.** For a point `x` of the polytope
and a randomized rounding of `p`, the displaced point `x + (p − rnd p)` leaves the
`κ`-inflation with probability at most `r · exp(-κ²/2)`.

Every hypothesis of `Arlib.KV97.escape_prob_le` is discharged by
`Arlib.Lattice.Rounding.{measurable_latDisp, iIndepFun_latDisp, ae_latDisp_mem_Icc,
integral_latDisp_eq_zero}`. -/
theorem roundLaw_escape_prob_le (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    (p : Fin n → ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    {κ r : ℝ} (hκ : 0 ≤ κ) (hr : (Fintype.card ι : ℝ) ≤ r) :
    (roundLaw p).real {z | x + latDispVec p z ∉ Polytope.inflate A b κ}
      ≤ r * Real.exp (-κ ^ 2 / 2) :=
  escape_prob_le A b (latDispVec p)
    (fun k => (measurable_latDisp p k).aemeasurable)
    (fun i => iIndepFun_latDisp p (fun k => A i k))
    (ae_latDisp_mem_Icc p) (integral_latDisp_eq_zero p) hx hκ hr

/-- **The escape bound for randomized rounding at `κ = kappaOf c r`.** The
constant is `exp(-c²/2)`; see the step-5 section docstring. -/
theorem roundLaw_escape_prob_le_exp (A : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    (p : Fin n → ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Polytope.body A b)
    {c r : ℝ} (hc : 0 ≤ c) (hr1 : 1 ≤ r) (hr : (Fintype.card ι : ℝ) ≤ r) :
    (roundLaw p).real {z | x + latDispVec p z ∉ Polytope.inflate A b (kappaOf c r)}
      ≤ Real.exp (-c ^ 2 / 2) :=
  le_trans (roundLaw_escape_prob_le A b p hx (kappaOf_nonneg hc) hr)
    (mul_exp_kappaOf_le hc hr1)

end RoundLaw

end Arlib.KV97
