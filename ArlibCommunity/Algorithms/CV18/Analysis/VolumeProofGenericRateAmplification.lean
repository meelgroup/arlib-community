import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGenericAmplification

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- Median amplification with an arbitrary explicit positive base-rate
envelope.  This is the soft-O form needed when a concrete walk construction
exposes additional logarithmic factors. -/
theorem oracleProgram_proof_amplification_of_rate
    (rate : VolumeParams → ℝ) (hrate : ∀ q, 1 ≤ rate q) :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
          (q : VolumeParams) (I : VolumeInput q.n)
          (oracle : MembershipOracle I),
          3 / 4 ≤ outcomeProbability
              (volumeAlgorithmLaw base q I oracle) (accurateOutcome q I) →
            (base q).StronglyMeasurable oracle.query →
            (∃ calls, (base q).QueryBound calls ∧
              calls ≤ Nat.ceil (C₀ * rate q)) →
              1 - q.p ≤ outcomeProbability
                  (volumeAlgorithmLaw (amplifyOracleProgram base) q I oracle)
                  (accurateOutcome q I) ∧
                ∃ calls,
                  (amplifyOracleProgram base q).QueryBound calls ∧
                  calls ≤ Nat.ceil
                    (C * (rate q * protectedLog (1 / q.p))) := by
  intro C₀ hC₀
  let C : ℝ := 9 * (C₀ + 1)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro base q I oracle hprob hmeas hcost
  let μ : Measure ℝ := (base q).runEstimate oracle.query
  let R : ℝ := rate q
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
    exact (Real.exp_le_exp.2 hstep).trans_eq (Real.exp_log q.hp.1)
  have haccuracy : 1 - q.p ≤
      outcomeProbability
        (volumeAlgorithmLaw (amplifyOracleProgram base) q I oracle)
        (accurateOutcome q I) := by
    have hsem := amplifyOracleProgram_semantics base q oracle.query hmeas
    rw [outcomeProbability_eq_measure]
    unfold volumeAlgorithmLaw
    rw [hsem.2, Measure.map_apply (measurable_medianOf _)
      (accurateOutcome_measurable q I)]
    exact le_trans (by linarith) hmedian
  refine ⟨haccuracy, ?_⟩
  obtain ⟨B, hBprogram, hB⟩ := hcost
  refine ⟨m * B, ?_, ?_⟩
  · simpa [m] using amplifyOracleProgram_queryBound base q hBprogram
  · have hR : 1 ≤ R := hrate q
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
      have hB' : B ≤ Nat.ceil (C₀ * R) := by simpa [R] using hB
      have hBceil : (B : ℝ) ≤ (Nat.ceil (C₀ * R) : ℝ) := by
        exact_mod_cast hB'
      nlinarith
    have hreal : ((m * B : ℕ) : ℝ) ≤ C * (rate q * protectedLog (1 / q.p)) := by
      rw [Nat.cast_mul]
      calc
        (m : ℝ) * (B : ℝ) ≤ (9 * L) * ((C₀ + 1) * R) :=
          mul_le_mul hm_real hB_real (Nat.cast_nonneg _) (by positivity)
        _ = C * (rate q * protectedLog (1 / q.p)) := by
          dsimp [C, R, L]
          ring
    exact_mod_cast le_trans hreal
      (Nat.le_ceil (C * (rate q * protectedLog (1 / q.p))) )

end ArlibCommunity.Algorithms.CV18
