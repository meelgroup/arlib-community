/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoMeasurableUncond
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.EllMollifier

/-!
# `thm:iso` for measurable sets at the **indicator** density `1_K·ℓ·γ`

`Arlib.ellGaussian_isoperimetry_measurable_logTwo_uncond`
(`Arlib/Convexity/IsoMeasurableUncond.lean:139`) proves Cousins–Vempala's `thm:iso` for
measurable `S₁, S₂, S₃` at the **continuous** density `ℓ·γ`, with no Lipschitz hypothesis.
The density the sampler's conductance bound actually consumes is the **indicator** one,

    h = 1_K · ℓ · γ,

fixed by `Arlib.MarkovChains.hpi_ellGaussian` inside
`Arlib.MarkovChains.conductance_speedyGaussian_ge`.  That density is *discontinuous* across
`∂K` — a boundary point of a convex body still has `ℓ ≥ 2⁻ⁿ > 0` while the indicator drops to
`0` — so it fails the capstone's `hhc`, and the mismatch is not one that monotonicity can
absorb: `∫ ℓγ > ∫ 1_K ℓγ` by the collar mass just outside `K`, and that collar lands on the
*right-hand* side of the inequality, where it hurts.

This file is the bridge, by mollification.  It is the `ℓ`-carrying analogue of what
`Arlib.gaussianIndicator_isoperimetry_measurable` (`Arlib/Convexity/IsoIndicator.lean:476`)
does for `1_K·γ`.

## Why the mollification closes, and where it differs from the indicator-only version

Run the measurable capstone at `g j = e^{−j·d(x, K̄)}·ℓ·γ` — continuous, log-concave-cofactored
(`Arlib.isLogConcave_expNegInfDist_mul_ell`), bounded by `1`, integrable — with the three
parts **cut to `K`**:

    S₁' = S₁ ∩ K,   S₂' = S₂ ∩ K,   S₃' = (S₁' ∪ S₂')ᶜ.

Three things then fall out, and the first is what the older route could not have:

* **The separation hypothesis transfers for free.**  On `K` one has `d(x, K̄) = 0`, hence
  `g j = ℓ·γ = h` pointwise there, so `densDist (g j) u v = densDist h u v` for all
  `u, v ∈ K` — *exactly*, for every `j`.  No comparison estimate is needed and the density
  branch is never touched.  `gaussianIndicator_isoperimetry_measurable` cannot do this: it has
  to force every pair into the metric branch first, which is what costs a Lipschitz constant.
* **Two of the three integrals do not move at all.**  `S₁', S₂' ⊆ K`, so
  `∫_{S₁'} g j = ∫_{S₁} h` for every `j`, and likewise for `S₂'`.
* **Only the mass and the residual take a limit**, and both land on the nose:
  `∫ g j → ∫_{K̄} ℓγ = ∫ h` and `∫_{S₃'} g j → ∫_{S₃} h`, the latter because
  `S₃' ∩ K = S₃ ∩ K` by the partition property, and `volume (frontier K) = 0` for convex `K`
  reconciles `K̄` with `K` (`Arlib.setIntegral_closure_eq_setIntegral`).

## What is proved here

* `Arlib.ellGaussianIndicator_isoperimetry_measurable_logTwo` — `thm:iso` for measurable
  `S₁, S₂, S₃` at `h = 1_K·ℓ·γ`, carrying **no** `hellLip`, **no** `hLσ`, and no `R` or `Lf`.

## Scope

This is an isoperimetric inequality, in the shape `hiso` of
`Arlib.MarkovChains.conductance_speedyGaussian_ge` wants.  Feeding it to that theorem, and
propagating the result to a mixing time and a running time, are separate steps and are **not**
performed here.  Nothing in this file may on its own be quoted as a conductance, mixing-time or
runtime bound.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib

open MeasureTheory Filter Topology Arlib.MarkovChains

variable {n : ℕ}

/-- **Cousins–Vempala's `thm:iso` for measurable `S₁, S₂, S₃`, at the indicator density
`h = 1_K·ℓ·γ`** — the density `Arlib.MarkovChains.conductance_speedyGaussian_ge` consumes.

Compare `Arlib.ellGaussian_isoperimetry_measurable_logTwo`
(`Arlib/Convexity/IsoWeighted.lean:851`), which reaches the measurable case by converting the
density branch of the separation disjunction into the metric branch and therefore carries

    hellLip : ∀ u ∈ K, ∀ v ∈ K, ℓ(u) ≤ ℓ(v)·exp(Lf·‖u − v‖)
    hLσ     : √3·(σ²·Lf + R) ≤ 2σ√n

for which `AUDIT.md` §0i(b) argues there is no witness with non-constant `ℓ` at the operative
step `δ ≤ σ/(8√n)`.  **Both are gone here, along with the parameters `R` and `Lf`.**

See the module docstring for why the mollification limit closes without any comparison
between `densDist (g j)` and `densDist h`. -/
theorem ellGaussianIndicator_isoperimetry_measurable_logTwo (hn : 2 ≤ n) {σ d δ : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (hδ : 0 < δ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ∀ x, h x = Set.indicator K
      (fun y => (ell K δ y).toReal * Real.exp (-‖y‖ ^ 2 / (2 * σ ^ 2))) x)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨ 4 * (d / σ) * Real.sqrt n ≤ densDist h u v) :
    d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x) ≤ (∫ x, h x) * ∫ x in S₃, h x := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    exact hK0 (by rw [hc]; exact measure_empty)
  -- the mollified family
  set g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun j x => Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
      * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) with hgdef
  have hg : ∀ (j : ℕ) (x : EuclideanSpace ℝ (Fin n)), g j x =
      Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal
        * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := fun _ _ => rfl
  -- on `K` the mollified density, the continuous one and the indicator one all agree
  have hgK : ∀ (j : ℕ), ∀ x ∈ K,
      g j x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
    intro j x hx
    have hz : Metric.infDist x (closure K) = 0 :=
      Metric.infDist_zero_of_mem (subset_closure hx)
    rw [hg, hz, mul_zero, Real.exp_zero, one_mul]
  have hhK : ∀ x ∈ K, h x = (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) :=
    fun x hx => by rw [hh, Set.indicator_of_mem hx]
  -- the parts, cut to `K`
  set S₁' : Set (EuclideanSpace ℝ (Fin n)) := S₁ ∩ K with hS₁'def
  set S₂' : Set (EuclideanSpace ℝ (Fin n)) := S₂ ∩ K with hS₂'def
  have hS₁'m : MeasurableSet S₁' := hS₁.inter hK
  have hS₂'m : MeasurableSet S₂' := hS₂.inter hK
  have hS₃'m : MeasurableSet (S₁' ∪ S₂')ᶜ := (hS₁'m.union hS₂'m).compl
  have hpart' : IsPartition3 Set.univ S₁' S₂' (S₁' ∪ S₂')ᶜ :=
    { union := Set.union_compl_self _
      disjoint₁₂ := hpart.disjoint₁₂.mono Set.inter_subset_left Set.inter_subset_left
      disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
      disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
  -- the residual, intersected with `K`, is exactly `S₃ ∩ K`
  have hres : (S₁' ∪ S₂')ᶜ ∩ K = S₃ ∩ K := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      refine ⟨?_, hxK⟩
      have hx1 : x ∉ S₁ := fun hc => hx (Or.inl ⟨hc, hxK⟩)
      have hx2 : x ∉ S₂ := fun hc => hx (Or.inr ⟨hc, hxK⟩)
      have hcover : x ∈ S₁ ∪ S₂ ∪ S₃ := by rw [hpart.union]; exact Set.mem_univ x
      rcases hcover with (h1 | h2) | h3
      · exact absurd h1 hx1
      · exact absurd h2 hx2
      · exact h3
    · rintro ⟨hx3, hxK⟩
      refine ⟨?_, hxK⟩
      rintro (⟨hc, -⟩ | ⟨hc, -⟩)
      · exact (Set.disjoint_left.mp hpart.disjoint₁₃ hc) hx3
      · exact (Set.disjoint_left.mp hpart.disjoint₂₃ hc) hx3
  -- the capstone, at each `j`
  have hmain : ∀ j : ℕ, d / σ * ((∫ x in S₁', g j x) * ∫ x in S₂', g j x)
      ≤ (∫ x, g j x) * ∫ x in (S₁' ∪ S₂')ᶜ, g j x := by
    intro j
    refine gaussianRestricted_isoperimetry_measurable_logTwo hn hσ hd
      (f := fun x => Real.exp (-(j : ℝ) * Metric.infDist x (closure K)) * (ell K δ x).toReal)
      (fun x => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
      (isLogConcave_expNegInfDist_mul_ell hK hKc hKb hKne δ j)
      (fun x => by rw [hg]) (hMoll_continuous hn0 hδ.le hg j) (hMoll_le_one hg j)
      (hMoll_integrable hn0 hδ.le hσ hg j) hpart' hS₁'m hS₂'m hS₃'m
      (hMoll_integral_pos hn0 hδ hσ hKc hKb hK0 hg j) ?_
    -- the separation, transferred verbatim because `g j = h` on `K`
    intro u hu v hv
    have hdd : densDist (g j) u v = densDist h u v := by
      rw [densDist, densDist, hgK j u hu.2, hgK j v hv.2, hhK u hu.2, hhK v hv.2]
    rw [hdd]
    exact hsep u hu.1 v hv.1
  -- the indicator density, read as an integral over `A ∩ K` of the continuous one
  have hHdK : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      (∫ x in A ∩ K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
        = ∫ x in A, h x := by
    intro A _
    simp only [hh]
    exact (setIntegral_eq_setIntegral_indicator (σ := σ) hK A).symm
  -- the two integrals that do not move
  have hfix : ∀ (j : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))), MeasurableSet A →
      (∫ x in A ∩ K, g j x) = ∫ x in A, h x := by
    intro j A hA
    rw [setIntegral_congr_fun (hA.inter hK) (fun x hx => hgK j x hx.2)]
    exact hHdK A hA
  -- the limits
  have hlim_mass : Tendsto (fun j : ℕ => ∫ x, g j x) atTop (𝓝 (∫ x, h x)) := by
    have h1 := tendsto_integral_hMoll hn0 hδ.le hσ hKne hg
    have h2 : (∫ x in closure K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
        = ∫ x, h x := by
      calc (∫ x in closure K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
          = ∫ x in Set.univ ∩ closure K,
              (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
            rw [Set.univ_inter]
        _ = ∫ x in Set.univ ∩ K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) :=
            setIntegral_closure_eq_setIntegral (δ := δ) (σ := σ) hK hKc Set.univ
        _ = ∫ x in Set.univ, h x := hHdK Set.univ MeasurableSet.univ
        _ = ∫ x, h x := setIntegral_univ
    rwa [h2] at h1
  have hlim_res : Tendsto (fun j : ℕ => ∫ x in (S₁' ∪ S₂')ᶜ, g j x) atTop
      (𝓝 (∫ x in S₃, h x)) := by
    have h1 := tendsto_setIntegral_hMoll hn0 hδ.le hσ hKne hg (S₁' ∪ S₂')ᶜ
    have h2 : (∫ x in (S₁' ∪ S₂')ᶜ ∩ closure K,
        (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))) = ∫ x in S₃, h x := by
      calc (∫ x in (S₁' ∪ S₂')ᶜ ∩ closure K,
            (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)))
          = ∫ x in (S₁' ∪ S₂')ᶜ ∩ K,
              (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) :=
            setIntegral_closure_eq_setIntegral (δ := δ) (σ := σ) hK hKc _
        _ = ∫ x in S₃ ∩ K, (ell K δ x).toReal * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) := by
            rw [hres]
        _ = ∫ x in S₃, h x := hHdK S₃ hS₃
    rwa [h2] at h1
  -- pass to the limit; the left-hand side never moved
  have hLHS : ∀ j : ℕ, d / σ * ((∫ x in S₁, h x) * ∫ x in S₂, h x)
      ≤ (∫ x, g j x) * ∫ x in (S₁' ∪ S₂')ᶜ, g j x := by
    intro j
    have := hmain j
    rwa [hS₁'def, hS₂'def, hfix j S₁ hS₁, hfix j S₂ hS₂] at this
  exact ge_of_tendsto (hlim_mass.mul hlim_res) (Eventually.of_forall hLHS)

section AxiomCheck

#print axioms Arlib.ellGaussianIndicator_isoperimetry_measurable_logTwo

end AxiomCheck

end Arlib
