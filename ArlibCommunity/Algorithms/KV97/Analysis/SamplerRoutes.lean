/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.KV97.Analysis.Theorem2
import ArlibCommunity.Foundations.MarkovChainTheory.PointwiseMixing.Analysis.PointwiseRoute
import ArlibCommunity.Foundations.MarkovChainTheory.BallWalkMixing.Analysis.BallWalkConductance

/-!
# Samplers that meet Kannan–Vempala's contract

Kannan–Vempala's Theorem 2 needs a continuous sampler on the inflated polytope.  This module
connects it to samplers the Markov-chain theory provides:

* a law within total variation `θ / V` of uniform gives the same two-sided window as a
  pointwise almost-uniform density (`theorem2_of_tvLe`, `theorem2_of_mixesWithin`);
* exact rejection from a superset meets the pointwise hypothesis at error `0`
  (`pointwiseAlmostUniform_of_rejection`);
* the lazy ball walk, run long enough from a warm start, meets it from an isoperimetric
  inequality for the body (`theorem2_of_lazy_ballWalk`).

These results moved here from the Markov-chain theory, which no longer depends on this
algorithm.

## Main results

* `theorem2_of_tvLe`, `theorem2_of_mixesWithin`
* `pointwiseAlmostUniform_of_rejection`
* `theorem2_of_lazy_ballWalk`
* `exists_theorem2_of_tvLe_witness`
-/

open ArlibCommunity.Foundations.Convex ArlibCommunity.Foundations.MarkovChainTheory ArlibCommunity.Foundations.MarkovChainTheory.PointwiseRoute

namespace ArlibCommunity.Algorithms.KV97

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

variable {n : ℕ}

/-! ## Route 3 applied: Kannan–Vempala Theorem 2 from a total-variation hypothesis

`ArlibCommunity.Algorithms.KV97.theorem2` takes a *density* `f` and computes `Pr[rnd p = x]` as
`∫_{P'} f p · prodTent x p dp`.  The statements below take the sampler's **law** `μ` and
compute the same quantity as `∫ prodTent x p ∂μ`.  The measure form is the primitive one —
a sampler returns a law, not a density — and it is strictly more general: a law with an
atom has no density at all, and `not_pointwiseClose_of_atom` below shows that is exactly
the situation of a ball walk started at a point.

The two forms agree whenever the law does have a density; for the uniform law this is
`integral_prodTent_uniformOn_eq_setIntegral` below, which is also the bridge route 2 uses. -/

section KV97



variable {n : ℕ}

/-- The rounding kernel is bounded by `1`: it is a product of `tent` values, and
`tent u = max (1 − |u|) 0 ≤ 1`.  This is what makes `ArlibCommunity.Foundations.Convex.TVLe.integral_le` applicable to
it — that lemma transfers `[0,1]`-valued observables, and `ArlibCommunity.Foundations.Lattice.Rounding` records
only `prodTent_nonneg`. -/
theorem prodTent_le_one (x p : EuclideanSpace ℝ (Fin n)) : prodTent x p ≤ 1 := by
  have h : ∀ i : Fin n, tent (p i - x i) ≤ 1 := by
    intro i
    have habs := abs_nonneg (p i - x i)
    simp only [tent]
    exact max_le (by linarith) zero_le_one
  simp only [prodTent]
  exact Finset.prod_le_one₀ (fun i _ => tent_nonneg _) fun i _ => h i

/-- The uniform average of the rounding kernel is the set integral over `S`, scaled by the
volume.  `ArlibCommunity.Foundations.Convex.integral_uniformOn_real`, specialised. -/
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

with `E` the escape mass — **exactly the shape `ArlibCommunity.Algorithms.KV97.theorem2` produces from its
pointwise hypothesis**, with `θ` in place of the pointwise `ε`.

This is what the pointwise-versus-total-variation discussion in `Algorithms/KV97/Analysis/Theorem2.lean` claims is impossible "at the required scale `1/Vol(P')`".
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
no density: `ArlibCommunity.Foundations.MarkovChainTheory.MixesWithin` is exactly what a conductance bound delivers,
and this is it being consumed. -/
theorem theorem2_of_mixesWithin {S : Set (EuclideanSpace ℝ (Fin n))}
    {P : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))} [IsMarkovKernel P]
    {μ₀ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ₀] {V E θ : ℝ}
    {t : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hS : MeasurableSet S)
    (h0 : volume S ≠ 0) (htop : volume S ≠ ⊤) (hVS : (volume S).toReal = V) (hθ : 0 ≤ θ)
    (hmix : ArlibCommunity.Foundations.MarkovChainTheory.MixesWithin P (uniformOn volume S) μ₀ t
      (ENNReal.ofReal (θ / V)))
    (hesc : ∫ p in Sᶜ, prodTent x p ≤ E) :
    (1 - (E + θ)) / V ≤ ∫ p, prodTent x p ∂(ArlibCommunity.Foundations.MarkovChainTheory.iterate P μ₀ t) ∧
      ∫ p, prodTent x p ∂(ArlibCommunity.Foundations.MarkovChainTheory.iterate P μ₀ t) ≤ (1 + θ) / V :=
  theorem2_of_tvLe_inv_volume hS h0 htop hVS hmix hθ hesc

end KV97

/-- **Route 2 discharges `ArlibCommunity.Algorithms.KV97.theorem2`'s hypothesis outright.**

Rejecting a uniform draw from a superset `B ⊇ P'` onto `P'` gives a law under which
`Pr[rnd p = x]` is *literally* the density-form integrand of `ArlibCommunity.Algorithms.KV97.theorem2` at the
constant density `1/V`, and that density is `ArlibCommunity.Algorithms.KV97.PointwiseAlmostUniform` at error
`0` — hence at every `ε ≥ 0`.  Nothing is approximated.

So the pointwise interface is not vacuous and not unreachable; it is only *expensive*.  See
`uniformOn_ball_ball` for how expensive. -/
theorem pointwiseAlmostUniform_of_rejection {n : ℕ}
    {B S : Set (EuclideanSpace ℝ (Fin n))} {V ε : ℝ} (hS : MeasurableSet S) (hSB : S ⊆ B)
    (hB0 : volume B ≠ 0) (hBtop : volume B ≠ ⊤) (hVS : (volume S).toReal = V) (hV : 0 < V)
    (hε : 0 ≤ ε) (x : EuclideanSpace ℝ (Fin n)) :
    ∫ p, ArlibCommunity.Algorithms.KV97.prodTent x p ∂(condOn (uniformOn volume B) S)
        = ∫ p in S, (1 / V) * ArlibCommunity.Algorithms.KV97.prodTent x p ∧
      ArlibCommunity.Algorithms.KV97.PointwiseAlmostUniform (fun _ => 1 / V) S V ε := by
  refine ⟨?_, ArlibCommunity.Algorithms.KV97.PointwiseAlmostUniform.uniform S hV hε⟩
  rw [condOn_uniformOn_eq_uniformOn volume hS hSB hB0 hBtop,
    integral_uniformOn_eq_setIntegral_const_mul, hVS]

/-! ## 11. The sampler contract: Kannan–Vempala Theorem 2 from a geometric hypothesis

`theorem2_of_mixesWithin` consumes a chain that has mixed in
total variation to tolerance `acc / Vol(K)` and returns Theorem 2's two-sided window.
Feeding it `mixesWithin_lazy_ballWalk` closes the chain from a geometric hypothesis about
`K` all the way to the sampler contract. -/

/-- **End to end: from an isoperimetric inequality for `K` to the KV97 Theorem 2 window.**

Run the lazy `δ`-ball walk on `K` from an `M`-warm start for
`conductanceMixingTime M (min (θ/32) (κθ²δ/(128n))) (acc/V)` steps; then for every lattice
point `x`, the rounding probability lies in the window `[(1−(E+acc))/V, (1+acc)/V]`.

Every hypothesis with content is inline: `hiso` is the isoperimetric inequality written out,
`hell` the uniform lower bound on the local conductance, `hesc` the escape mass of the tent
outside `K`, `hwarm` the warm start.  The two honest caveats of
`mixesWithin_lazy_ballWalk` apply verbatim: the constant is a factor `√n` worse than
Cousins–Vempala's because Mathlib lacks the ball-cap volume estimate, and `hell` is forced
rather than a proof artefact — its only *proved* witness is `θ = 2⁻ⁿ` on the unit ball, so
the step count this theorem certifies is exponential in `n` unless the caller supplies a
better `θ`. -/
theorem theorem2_of_lazy_ballWalk (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d * ArlibCommunity.Foundations.Convex.uniformOn volume K A
          * ArlibCommunity.Foundations.Convex.uniformOn volume K B
        ≤ ArlibCommunity.Foundations.Convex.uniformOn volume K ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ArlibCommunity.Foundations.Convex.uniformOn volume K))
    {V acc E : ℝ} (hV : (volume K).toReal = V) (hacc : 0 < acc)
    {x : EuclideanSpace ℝ (Fin n)}
    (hesc : ∫ p in Kᶜ, ArlibCommunity.Algorithms.KV97.prodTent x p ≤ E)
    {t : ℕ}
    (ht : conductanceMixingTime M (min (θ / 32) (kappa * θ ^ 2 * δ / (128 * (n : ℝ))))
      (acc / V) ≤ t) :
    (1 - (E + acc)) / V
        ≤ ∫ p, ArlibCommunity.Algorithms.KV97.prodTent x p
            ∂(iterate (lazy (ballWalk K δ)) mu0 t) ∧
      ∫ p, ArlibCommunity.Algorithms.KV97.prodTent x p
          ∂(iterate (lazy (ballWalk K δ)) mu0 t) ≤ (1 + acc) / V := by
  have hVpos : 0 < V := hV ▸ ENNReal.toReal_pos hK0 hKtop
  exact theorem2_of_mixesWithin hK hK0 hKtop hV hacc.le
    (mixesWithin_lazy_ballWalk hn hK hK0 hKtop hδ hθ hell hkappa hiso hM hwarm
      (by positivity) ht)
    hesc

/-! ## Non-vacuity

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
        (∫ p in Sᶜ, ArlibCommunity.Algorithms.KV97.prodTent x p) ≤ E ∧
        ((1 - (E + θ)) / V ≤ ∫ p, ArlibCommunity.Algorithms.KV97.prodTent x p ∂μ ∧
          (∫ p, ArlibCommunity.Algorithms.KV97.prodTent x p ∂μ) ≤ (1 + θ) / V) := by
  set S : Set (EuclideanSpace ℝ (Fin (n + 1))) := Metric.ball 0 1 with hSdef
  have hS : MeasurableSet S := measurableSet_ball
  have h0 : volume S ≠ 0 := (Metric.measure_ball_pos volume 0 one_pos).ne'
  have htop : volume S ≠ ⊤ := measure_ball_ne_top
  have hV : 0 < (volume S).toReal := ENNReal.toReal_pos h0 htop
  haveI : IsProbabilityMeasure (uniformOn volume S) :=
    isProbabilityMeasure_uniformOn volume h0 htop
  refine ⟨S, uniformOn volume S, (volume S).toReal,
    ∫ p in Sᶜ, ArlibCommunity.Algorithms.KV97.prodTent x p, inferInstance, hS, h0, htop, rfl, hV,
    (ArlibCommunity.Foundations.Convex.TVLe.refl _).mono (by simp), le_rfl, ?_⟩
  exact theorem2_of_tvLe_inv_volume hS h0 htop rfl ((ArlibCommunity.Foundations.Convex.TVLe.refl _).mono (by simp)) hθ le_rfl

end ArlibCommunity.Algorithms.KV97
