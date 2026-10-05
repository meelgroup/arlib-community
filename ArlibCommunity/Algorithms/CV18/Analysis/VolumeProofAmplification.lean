/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.MeasureAmplification

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- Median amplification for the measure-valued oracle interpreter. -/
theorem volume_proof_amplification :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : VolumeCoolingPrimitives)
          (S : (q : VolumeParams) → VolumeCoolingSchedule q)
          (q : VolumeParams) (I : VolumeInput q.n)
          (oracle : MembershipOracle I),
          3 / 4 ≤
              outcomeProbability
                (volumeAlgorithmLaw (fun q => baseVolumeCooling P S q) q I oracle)
                (accurateOutcome q I) →
            (baseVolumeCooling P S q).StronglyMeasurable oracle.query →
            (∃ calls,
              (baseVolumeCooling P S q).QueryBound calls ∧
              calls ≤
                Nat.ceil
                  (C₀ * volumeBaseComplexityRate q)) →
              1 - q.p ≤
                  outcomeProbability
                    (volumeAlgorithmLaw (volumeCoolingAlgorithm P S) q I oracle)
                    (accurateOutcome q I) ∧
                ∃ calls,
                  (volumeCoolingAlgorithm P S q).QueryBound calls ∧
                  calls ≤ Nat.ceil (C * volumeComplexityRate q) := by
  intro C₀ hC₀
  let C : ℝ := 9 * (C₀ + 1)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro P S q I oracle hprob hmeas hcost
  let μ : Measure ℝ := (baseVolumeCooling P S q).runEstimate oracle.query
  let R : ℝ := volumeBaseComplexityRate q
  let L : ℝ := protectedLog (1 / q.p)
  let m : ℕ := confidenceRepetitions q

  let _ : IsProbabilityMeasure μ :=
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      hmeas.estimateMeasurable

  have haccuracySet : accurateOutcome q I =
      Set.Icc (euclideanVolume I - q.eps * euclideanVolume I)
        (euclideanVolume I + q.eps * euclideanVolume I) := by
    unfold accurateOutcome RelativeApprox Arlib.relErr
    ext estimate
    simp only [Set.mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

  have hbaseProb : 3 / 4 ≤ (μ (accurateOutcome q I)).toReal := by
    rw [outcomeProbability_eq_measure] at hprob
    simpa [μ, volumeAlgorithmLaw] using hprob

  have hmedian : 1 - Real.exp (-(m : ℝ) / 8) ≤
      (repeatEstimateMeasure μ m
        {v | Arlib.Probability.medianOf v ∈ accurateOutcome q I}).toReal := by
    rw [haccuracySet]
    exact repeatEstimateMeasure_median_Icc_ge μ m (by
      simpa [haccuracySet] using hbaseProb)

  have hexp : Real.exp (-(m : ℝ) / 8) ≤ q.p := by
    have hlog : Real.log (1 / q.p) ≤ protectedLog (1 / q.p) := le_max_right _ _
    have hm : 8 * Real.log (1 / q.p) ≤ (m : ℝ) := by
      unfold m confidenceRepetitions
      exact le_trans (by linarith) (Nat.le_ceil _)
    have hstep : -(m : ℝ) / 8 ≤ Real.log q.p := by
      rw [show Real.log (1 / q.p) = -Real.log q.p by
        rw [one_div, Real.log_inv]] at hm
      linarith
    calc
      Real.exp (-(m : ℝ) / 8) ≤ Real.exp (Real.log q.p) :=
        Real.exp_le_exp.2 hstep
      _ = q.p := Real.exp_log q.hp.1

  have haccuracy : 1 - q.p ≤
      outcomeProbability
        (volumeAlgorithmLaw (volumeCoolingAlgorithm P S) q I oracle)
        (accurateOutcome q I) := by
    have hsem := volumeCoolingAlgorithm_semantics P S q oracle.query hmeas
    rw [outcomeProbability_eq_measure]
    unfold volumeAlgorithmLaw
    rw [hsem.2]
    rw [Measure.map_apply (measurable_medianOf _) (accurateOutcome_measurable q I)]
    exact le_trans (by linarith) hmedian

  refine ⟨haccuracy, ?_⟩
  obtain ⟨B, hBprogram, hB⟩ := hcost
  refine ⟨m * B, ?_, ?_⟩
  · simpa [m] using volumeCoolingAlgorithm_queryBound P S q hBprogram
  · have hR : 1 ≤ R := by
      have hn : 1 ≤ (q.n : ℝ) := by
        exact_mod_cast (le_trans (by omega : 1 ≤ 3) q.dim_ok)
      have hn3 : 1 ≤ (q.n : ℝ) ^ 3 := one_le_pow₀ hn
      have hepssq : 0 < q.eps ^ 2 := sq_pos_of_pos q.heps.1
      have hepssq_le : q.eps ^ 2 ≤ 1 := by nlinarith [q.heps.1, q.heps.2]
      have hmax : 1 ≤ max 1 q.roundness := le_max_left _ _
      have hmul : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
        intro a b ha hb
        nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
      have hfirst : 1 ≤ max 1 q.roundness * (q.n : ℝ) ^ 3 / q.eps ^ 2 := by
        rw [le_div_iff₀ hepssq]
        have h := le_trans hepssq_le (hmul hmax hn3)
        simpa only [one_mul] using h
      have hloge : 1 ≤ protectedLog (1 / q.eps) := le_max_left _ _
      have hlogne : 1 ≤ protectedLog ((q.n : ℝ) / q.eps) := le_max_left _ _
      have hlogt : 1 ≤ protectedLog (volumeTerminalScale q) := le_max_left _ _
      dsimp [R]
      exact hmul (hmul (hmul hfirst (one_le_pow₀ hloge))
        (one_le_pow₀ hlogne)) (one_le_pow₀ hlogt)
    have hL : 1 ≤ L := le_max_left _ _
    have hm_nonneg : 0 ≤ 8 * L := by positivity
    have hm_real : (m : ℝ) ≤ 9 * L := by
      have hceil : (m : ℝ) < 8 * L + 1 := by
        simpa [m, confidenceRepetitions, L] using Nat.ceil_lt_add_one hm_nonneg
      linarith
    have hraw_nonneg : 0 ≤ C₀ * R := mul_nonneg hC₀.le (by linarith)
    have hceil_real : ((Nat.ceil (C₀ * R) : ℕ) : ℝ) < C₀ * R + 1 := by
      simpa using Nat.ceil_lt_add_one hraw_nonneg
    have hB_real : (B : ℝ) ≤ (C₀ + 1) * R := by
      have hB' : B ≤ Nat.ceil (C₀ * R) := by
        simpa [R, Nat.cast_pow] using hB
      have hBceil : (B : ℝ) ≤ (Nat.ceil (C₀ * R) : ℝ) := by exact_mod_cast hB'
      nlinarith
    have hreal : ((m * B : ℕ) : ℝ) ≤ C * volumeComplexityRate q := by
      rw [Nat.cast_mul]
      calc
        (m : ℝ) * (B : ℝ) ≤ (9 * L) * ((C₀ + 1) * R) :=
          mul_le_mul hm_real hB_real (Nat.cast_nonneg _) (by positivity)
        _ = C * volumeComplexityRate q := by
          dsimp [C, R, L, volumeComplexityRate]
          ring
    exact_mod_cast le_trans hreal (Nat.le_ceil (C * volumeComplexityRate q))

end ArlibCommunity.Algorithms.CV18
