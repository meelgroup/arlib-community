/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoIndicatorEll
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.OverlapPerPair

/-!
# The speedy Metropolis–Gaussian conductance bound, unconditionally

`Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge_perPair`
(`Arlib/MarkovChains/Continuous/OverlapPerPair.lean:361`) is Cousins–Vempala's
`thm:speedyconductance` (`1409.6011/vol3_journal.tex:624`) with the comparability premise
`hcomp` discharged — but it still carries

    hellLip : ∀ u ∈ K, ∀ v ∈ K, ℓ(u) ≤ ℓ(v)·exp(Lf·‖u − v‖)
    hLσ     : √3·(σ²·Lf + R) ≤ 2σ√n

which `AUDIT.md` §0i(b) argues admit no witness with non-constant `ℓ` at the operative step
`δ ≤ σ/(8√n)`: `hLσ` caps `Lf` far below the rate `≈ √n·log 2/δ` that a corner forces, and
`Arlib.MarkovChains.two_pow_mul_ell_cube_corner_le_one` puts a corner in every consumer's
class.

**This file removes them.**  They entered only through the isoperimetric binder `hiso`, and
`Arlib.ellGaussianIndicator_isoperimetry_measurable_logTwo`
(`Arlib/Convexity/IsoIndicatorEll.lean`) now supplies `hiso` at the indicator density
`1_K·ℓ·γ` with no Lipschitz hypothesis of any kind.

## What is proved here

* `Arlib.hiso_speedyMetropolisGaussian_uncond` — the `hiso` binder of
  `Arlib.MarkovChains.conductance_speedyGaussian_ge`, character for character, with
  `hellLip`, `hLσ`, `hKR`, and the parameters `R` and `Lf` all **removed**.
* `Arlib.conductance_speedyMetropolisGaussian_ge_uncond` —

      Φ(speedyMetropolisGaussian K δ σ²)  ≥  δ·log 2 / (640·σ·√n)

  with respect to `Arlib.MarkovChains.ellGaussianProb K δ σ²`, carrying **no** isoperimetric
  and **no** comparability hypothesis.  Its binders are those of `_perPair` minus
  `hLf`, `hellLip`, `hLσ`.

## Scope — read before quoting

This is a conductance bound.  It is **not** a mixing time and **not** a running time; those
need the conductance-to-TV step and the speedy-to-target transfer, which are separate and are
not performed here.  `R` survives in the binders because the *overlap* side still needs it,
through the acceptance floor `Arlib.MarkovChains.acceptance_floor_of_cv`; only the
isoperimetry side became `R`-free.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib

open MeasureTheory Arlib.MarkovChains

variable {n : ℕ}

/-- **The `hiso` binder of `Arlib.MarkovChains.conductance_speedyGaussian_ge`, with no
Lipschitz hypothesis.**

This is `Arlib.MarkovChains.hiso_speedyMetropolisGaussian`
(`Arlib/MarkovChains/Continuous/SpeedyGaussianConductance.lean:230`) with `hLf`, `hKR`,
`hellLip`, `hLσ` and the parameters `R`, `Lf` **deleted**.  The conclusion is verbatim.

It is `Arlib.ellGaussianIndicator_isoperimetry_measurable_logTwo` at
`d := δ·log 2/√n`, which is positive exactly when `δ` is. -/
theorem hiso_speedyMetropolisGaussian_uncond (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0) :
    ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K
                (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y)) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K
                (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
            * ∫ x in S₂, Set.indicator K
                (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
        ≤ (∫ x, Set.indicator K
              (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in S₃, Set.indicator K
              (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x := by
  intro S₁ S₂ S₃ hpart hS₁ hS₂ hS₃ hsep
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  have hd : 0 < δ * Real.log 2 / Real.sqrt n := by positivity
  exact ellGaussianIndicator_isoperimetry_measurable_logTwo hn hσ hd hδ hK hKc hKb hK0
    (fun x => by simp [gaussianWeightReal]) hpart hS₁ hS₂ hS₃ hsep

/-- **`thm:speedyconductance` with no isoperimetric and no comparability hypothesis.**

`Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge_perPair`
(`Arlib/MarkovChains/Continuous/OverlapPerPair.lean:361`) with `hLf`, `hellLip` and `hLσ`
**removed** — and with them the parameter `Lf`.  Every other binder, and the conclusion

    Φ  ≥  δ·log 2 / (640·σ·√n),

are verbatim.

`R` remains, but only for the overlap side: it feeds
`Arlib.MarkovChains.acceptance_floor_of_cv` and `lem:f-dist`'s geometry
(`Arlib.MarkovChains.ell_comparable_of_densDist`).  The isoperimetry side no longer mentions
it.

**Still not a mixing time.**  See the module docstring. -/
theorem conductance_speedyMetropolisGaussian_ge_uncond (hn : 21 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance (speedyMetropolisGaussian K δ (σ ^ 2)) (ellGaussianProb K δ (σ ^ 2)) := by
  have hn2 : 2 ≤ n := by omega
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hR4 : R ≤ 4 * σ * Real.sqrt n := by
    have := Real.sqrt_nonneg (n : ℝ)
    nlinarith
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  exact conductance_speedyGaussian_ge hn2 hσ hδ hδσ
    (fun x => Set.indicator_nonneg
      (fun y _ => mul_nonneg ENNReal.toReal_nonneg (gaussianWeightReal_pos _ y).le) x)
    (integral_ellGaussianIndicator_pos hs hK hKc hKb hK0 hKtop hδ)
    hK (speedyMetropolisGaussian K δ (σ ^ 2)) (ellGaussianProb K δ (σ ^ 2))
    (hpi_ellGaussian hs hK hKtop δ)
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    (ellGaussianProb_compl_eq_zero hK δ (σ ^ 2))
    (hoverlap_speedyMetropolisGaussian_perPair hn hK hKc hKb hK0 hσ hδ hδσ hR hKR hR4
      (acceptance_floor_of_cv hn2 hσ hδ hδσ hRσ))
    (hiso_speedyMetropolisGaussian_uncond hn2 hσ hδ hK hKc hKb hK0)

/-- **Non-vacuity (`CLAUDE.md` §11): every binder of
`Arlib.conductance_speedyMetropolisGaussian_ge_uncond` is satisfied simultaneously**, at

    n = 21,  K = B̄(0,1),  σ = 100,  δ = 1,  R = 1.

The step cap reads `1 ≤ 100/(8√21)`, true since `√21 ≤ 5` gives `100/(8√21) ≥ 2.5`, and the
radius cap `1 ≤ 200√21` has enormous room.

This matters more than a routine witness would.  The binders this theorem *drops* —
`hellLip` and `hLσ` — are the ones `AUDIT.md` §0i(b) argues have **no** witness with
non-constant `ℓ`, so its predecessor
`Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge_perPair` had no unconditional
instance at all.  Here the bundle is met at `δ = 1` against a body of radius `1`.

*Unproven remark* (prose, not machine-checked): at those parameters `ℓ` is genuinely
non-constant on `K` — it is `1` at the centre and strictly less on the boundary, where the
proposal ball meets `K` in a lens.  The formal content of this theorem is the binder bundle
and the conclusion; the non-constancy is stated only to explain why the witness is not of the
degenerate kind that `Arlib.ellGaussian_isoperimetry_measurable_logTwo_strict_witness` is. -/
theorem conductance_speedyMetropolisGaussian_ge_uncond_witness :
    ∃ (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m))) (σ δ R : ℝ),
      21 ≤ m ∧ 0 < σ ∧ 0 < δ ∧ δ ≤ σ / (8 * Real.sqrt m) ∧
      MeasurableSet K ∧ Convex ℝ K ∧ volume K ≠ 0 ∧ 0 ≤ R ∧
      (∀ x ∈ K, ‖x‖ ≤ R) ∧ R ≤ 2 * σ * Real.sqrt m ∧
      ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt m))
        ≤ conductance (speedyMetropolisGaussian K δ (σ ^ 2))
            (ellGaussianProb K δ (σ ^ 2)) := by
  classical
  have hcast : Real.sqrt ((21 : ℕ) : ℝ) = Real.sqrt (21 : ℝ) := by norm_num
  have hnn : (0 : ℝ) ≤ Real.sqrt (21 : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (21 : ℝ) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h4 : (4 : ℝ) ≤ Real.sqrt (21 : ℝ) := by nlinarith
  have h5 : Real.sqrt (21 : ℝ) ≤ 5 := by nlinarith
  set K : Set (EuclideanSpace ℝ (Fin 21)) := Metric.closedBall 0 1 with hKdef
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hKc : Convex ℝ K := convex_closedBall _ _
  have hK0 : volume K ≠ 0 := by
    have : 0 < volume K :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by norm_num : (0 : ℝ) < 1))
        (measure_mono Metric.ball_subset_closedBall)
    exact this.ne'
  have hKR : ∀ x ∈ K, ‖x‖ ≤ 1 := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hδσ : (1 : ℝ) ≤ 100 / (8 * Real.sqrt ((21 : ℕ) : ℝ)) := by
    rw [hcast, le_div_iff₀ (by positivity)]
    linarith
  have hRσ : (1 : ℝ) ≤ 2 * 100 * Real.sqrt ((21 : ℕ) : ℝ) := by
    rw [hcast]; linarith
  exact ⟨21, K, 100, 1, 1, le_refl _, by norm_num, by norm_num, hδσ, hKm, hKc, hK0,
    by norm_num, hKR, hRσ,
    conductance_speedyMetropolisGaussian_ge_uncond (le_refl 21) (by norm_num) (by norm_num)
      hδσ hKm hKc hK0 (by norm_num) hKR hRσ⟩

section AxiomCheck

#print axioms Arlib.hiso_speedyMetropolisGaussian_uncond
#print axioms Arlib.conductance_speedyMetropolisGaussian_ge_uncond_witness
#print axioms Arlib.conductance_speedyMetropolisGaussian_ge_uncond

end AxiomCheck

end Arlib
