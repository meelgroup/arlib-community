/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.KV97.Model.ProblemSetting
import ArlibCommunity.Algorithms.KV97.Analysis.PseudocodeProof
import ArlibCommunity.Algorithms.KV97.Analysis.HitProbability

/-!
# Proof of Kannan–Vempala Theorem 2 for the program

`PseudocodeProof.output_singleton` writes the output probability as an integral against the
sampler.  With the sampler's density `f` this is `∫_{P'} f · prodTent x`, which is exactly the
quantity `hitProbability_bounds_of_body` bounds.
-/

namespace ArlibCommunity.Algorithms.KV97.TheoremProof

open MeasureTheory

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The output probability of `x`, for a sampler with density `f` on `S`, is
`∫_S f · prodTent x`. -/
theorem output_singleton_toReal {S : Set (State n)} (hS : MeasurableSet S)
    {f : State n → ℝ} (hf : Measurable f) {V ε : ℝ} (hV : 0 < V) (hε1 : ε ≤ 1)
    (hfS : PointwiseAlmostUniform f S V ε) (x : LatticePoint n) :
    (output ((volume.restrict S).withDensity (fun q => ENNReal.ofReal (f q))) {x}).toReal =
      ∫ q in S, f q * prodTent (toState x) q := by
  have hf0 : ∀ q ∈ S, 0 ≤ f q := fun q hq =>
    le_trans (div_nonneg (by linarith) hV.le) (hfS.lower hq)
  have hint : IntegrableOn (fun q => f q * prodTent (toState x) q) S := by
    refine Integrable.bdd_mul (c := (1 + ε) / V) (integrable_prodTent _).integrableOn
      hf.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun q hq => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 q hq)]
    exact hfS.upper hq
  rw [PseudocodeProof.output_singleton,
    lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal
      (measurable_prodTent _).ennreal_ofReal]
  have hcongr : ∫⁻ q in S, ((fun q => ENNReal.ofReal (f q)) *
      fun q => ENNReal.ofReal (prodTent (toState x) q)) q
      = ∫⁻ q in S, ENNReal.ofReal (f q * prodTent (toState x) q) := by
    refine setLIntegral_congr_fun hS fun q hq => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hf0 q hq)]
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hint, ENNReal.toReal_ofReal]
  · exact setIntegral_nonneg hS fun q hq => mul_nonneg (hf0 q hq) (prodTent_nonneg _ _)
  · exact (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun q hq =>
      mul_nonneg (hf0 q hq) (prodTent_nonneg _ _))

/-- Kannan–Vempala Theorem 2 for the program `output`. -/
theorem latticePoint_probability (p : Problem n ι)
    {sampler : Measure (State n)} {V ε : ℝ} (hV : 0 < V) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs : AlmostUniformSampler sampler p.inflatedBody V ε)
    {x : LatticePoint n} (hx : toState x ∈ p.body) :
    (1 - ε) * (1 - Real.exp (-p.c ^ 2 / 2)) / V ≤ (output sampler {x}).toReal ∧
      (output sampler {x}).toReal ≤ (1 + ε) / V := by
  obtain ⟨f, hf, hfS, rfl⟩ := hs
  have hS : MeasurableSet p.inflatedBody := measurableSet_inflated _ _ _ _
  have hf0 : ∀ q ∈ p.inflatedBody, 0 ≤ f q := fun q hq =>
    le_trans (div_nonneg (by linarith) hV.le) (hfS.lower hq)
  have hint : IntegrableOn (fun q => f q * prodTent (toState x) q) p.inflatedBody := by
    refine Integrable.bdd_mul (c := (1 + ε) / V) (integrable_prodTent _).integrableOn
      hf.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun q hq => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 q hq)]
    exact hfS.upper hq
  rw [output_singleton_toReal hS hf hV hε1 hfS]
  exact hitProbability_bounds_of_body hV (by linarith) hε1 hfS hint hx p.c_nonneg p.one_le_r p.card_le_r

end ArlibCommunity.Algorithms.KV97.TheoremProof
