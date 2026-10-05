/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ArlibCommunity.External.Kr25.Ttc.Volume.LVNormTailExplicitDyadic

/-! # Uniform-volume consequences for the explicit logarithmic LV radius -/

namespace Ttc.CVAdaptive

open MeasureTheory Metric Set
open Arlib Arlib.MarkovChains
open scoped ENNReal

variable {n : ℕ}

theorem volume_sdiff_explicitDyadicMomentRadius_toReal_le
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    {M eta : ℝ} (hM : 0 < M) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0) :
    (volume (K \ closedBall 0 (explicitDyadicMomentRadius M eta))).toReal ≤
      eta * (volume K).toReal := by
  let O : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | explicitDyadicMomentRadius M eta < ‖x‖}
  have hO : MeasurableSet O :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hKtop : volume K ≠ ⊤ :=
    (Metric.isCompact_of_isClosed_isBounded hKcl hKb).measure_lt_top.ne
  have hIon : IntegrableOn (O.indicator (fun _ => (1 : ℝ))) K :=
    (integrableOn_const hKtop).indicator hO
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) =>
      1 / (2 : ℝ) ^ explicitDyadicTailIndex eta) K := integrableOn_const hKtop
  have h := body_normTail_explicit_dyadic hn hKc hKcl hKb hM heta0 heta1 hmoment
  change (∫ x in K, O.indicator (fun _ => (1 : ℝ)) x -
    1 / (2 : ℝ) ^ explicitDyadicTailIndex eta) ≤ 0 at h
  have hreal : (volume (K ∩ O)).toReal ≤
      (1 / (2 : ℝ) ^ explicitDyadicTailIndex eta) * (volume K).toReal := by
    rw [show (∫ x in K, O.indicator (fun _ => (1 : ℝ)) x -
          1 / (2 : ℝ) ^ explicitDyadicTailIndex eta) =
        (∫ x in K, O.indicator (fun _ => (1 : ℝ)) x) -
          ∫ _x in K, (1 / (2 : ℝ) ^ explicitDyadicTailIndex eta) by
      rw [integral_sub hIon hconst]] at h
    have hcint : (∫ _x : EuclideanSpace ℝ (Fin n) in K,
        (1 / (2 : ℝ) ^ explicitDyadicTailIndex eta)) =
        (1 / (2 : ℝ) ^ explicitDyadicTailIndex eta) * (volume K).toReal := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def]
      ring
    rw [setIntegral_indicator hO, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def] at h
    rw [hcint] at h
    exact sub_nonpos.mp h
  have hset : K \ closedBall 0 (explicitDyadicMomentRadius M eta) = K ∩ O := by
    ext x
    simp [O, mem_closedBall]
  rw [hset]
  exact hreal.trans (mul_le_mul_of_nonneg_right
    (inv_two_pow_explicitDyadicTailIndex_le heta0 heta1) ENNReal.toReal_nonneg)

theorem volume_sdiff_explicitDyadicMomentRadius_div_le
    (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKb : Bornology.IsBounded K)
    (hK0 : volume K ≠ 0) {M eta : ℝ} (hM : 0 < M)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hmoment : (∫ x in K, (‖x‖ ^ 2 - M)) = 0) :
    volume (K \ closedBall 0 (explicitDyadicMomentRadius M eta)) / volume K ≤
      ENNReal.ofReal eta := by
  have hKtop : volume K ≠ ⊤ :=
    (Metric.isCompact_of_isClosed_isBounded hKcl hKb).measure_lt_top.ne
  have hSsub : K \ closedBall 0 (explicitDyadicMomentRadius M eta) ⊆ K := sdiff_subset
  have hStop : volume (K \ closedBall 0 (explicitDyadicMomentRadius M eta)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hSsub) (lt_top_iff_ne_top.2 hKtop))
  rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top hStop hK0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_div, ENNReal.toReal_ofReal heta0.le]
  apply (div_le_iff₀ (ENNReal.toReal_pos hK0 hKtop)).2
  exact volume_sdiff_explicitDyadicMomentRadius_toReal_le hn hKc hKcl hKb hM
    heta0 heta1 hmoment

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.volume_sdiff_explicitDyadicMomentRadius_div_le
