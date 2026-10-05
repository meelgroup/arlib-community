import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAmplification

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory

/-- Repeat an arbitrary real-valued oracle program independently. -/
noncomputable def repeatOracleProgram {n : ℕ}
    (base : MembershipOracleProgram n ℝ) :
    (m : ℕ) → MembershipOracleProgram n (Fin m → ℝ)
  | 0 => .pure Fin.elim0
  | m + 1 =>
      base.bind fun estimate =>
        (repeatOracleProgram base m).bind fun tail =>
          .pure (Fin.cons estimate tail)

/-- Median amplification of an arbitrary parameterized base program. -/
noncomputable def amplifyOracleProgram
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ) :
    VolumeAlgorithm :=
  fun q =>
    (repeatOracleProgram (base q) (confidenceRepetitions q)).bind fun estimates =>
      .pure (Arlib.Probability.medianOf estimates)

theorem repeatOracleProgram_queryBound {n : ℕ}
    (base : MembershipOracleProgram n ℝ) {budget : ℕ}
    (hbase : base.QueryBound budget) : ∀ repetitions,
      (repeatOracleProgram base repetitions).QueryBound (repetitions * budget) := by
  intro repetitions
  induction repetitions with
  | zero =>
      simpa [repeatOracleProgram] using
        (MembershipOracleProgram.QueryBound.pure
          (Result := Fin 0 → ℝ) Fin.elim0 0)
  | succ repetitions ih =>
      rw [repeatOracleProgram]
      have htail : ∀ estimate : ℝ,
          ((repeatOracleProgram base repetitions).bind fun tail =>
            .pure (Fin.cons estimate tail : Fin (repetitions + 1) → ℝ)).QueryBound
              (repetitions * budget) := by
        intro estimate
        simpa using ih.bind
          (fun tail => MembershipOracleProgram.QueryBound.pure _ 0)
      have h := hbase.bind htail
      simpa [Nat.succ_mul, Nat.add_comm] using h

theorem amplifyOracleProgram_queryBound
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) {budget : ℕ} (hbase : (base q).QueryBound budget) :
    (amplifyOracleProgram base q).QueryBound
      (confidenceRepetitions q * budget) := by
  unfold amplifyOracleProgram
  simpa using
    (repeatOracleProgram_queryBound (base q) hbase (confidenceRepetitions q)).bind
      (fun estimates => MembershipOracleProgram.QueryBound.pure _ 0)

theorem repeatOracleProgram_semantics {n : ℕ}
    (base : MembershipOracleProgram n ℝ)
    (oracle : AmbientSpace n → Bool)
    (hbase : base.StronglyMeasurable oracle) : ∀ repetitions,
      (repeatOracleProgram base repetitions).StronglyMeasurable oracle ∧
        (repeatOracleProgram base repetitions).runEstimate oracle =
          repeatEstimateMeasure (base.runEstimate oracle) repetitions := by
  let _ : IsProbabilityMeasure (base.runEstimate oracle) :=
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle _
      hbase.estimateMeasurable
  intro repetitions
  induction repetitions with
  | zero =>
      constructor
      · trivial
      · rfl
  | succ repetitions ih =>
      let _ : IsProbabilityMeasure
          (repeatEstimateMeasure (base.runEstimate oracle) repetitions) :=
        repeatEstimateMeasure_isProbabilityMeasure _ repetitions
      let tail := repeatOracleProgram base repetitions
      have hpureStrong (estimate : ℝ) : ∀ tailValues : Fin repetitions → ℝ,
          (MembershipOracleProgram.pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).StronglyMeasurable
              oracle := fun _ => trivial
      have hpureRun (estimate : ℝ) : Measurable fun tailValues : Fin repetitions → ℝ =>
          (MembershipOracleProgram.pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle := by
        simp only [MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp
          ((measurable_finCons repetitions).comp
            ((measurable_const : Measurable fun _ : (Fin repetitions → ℝ) => estimate).prodMk
              measurable_id))
      have hinnerStrong (estimate : ℝ) :
          (tail.bind fun tailValues => .pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).StronglyMeasurable
              oracle := ih.1.bind (hpureStrong estimate) (hpureRun estimate)
      have hinnerLaw (estimate : ℝ) :
          (tail.bind fun tailValues => .pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle =
          (repeatEstimateMeasure (base.runEstimate oracle) repetitions).map
            fun tailValues =>
              (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ) := by
        rw [MembershipOracleProgram.runEstimate_bind oracle tail _ ih.1
          (hpureStrong estimate) (hpureRun estimate)]
        rw [ih.2]
        exact Measure.bind_dirac_eq_map _
          ((measurable_finCons repetitions).comp
            ((measurable_const : Measurable fun _ : (Fin repetitions → ℝ) => estimate).prodMk
              measurable_id))
      have htailRun : Measurable fun estimate : ℝ =>
          (tail.bind fun tailValues => .pure
            (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle := by
        rw [show (fun estimate : ℝ =>
            (tail.bind fun tailValues => .pure
              (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle) =
            (fun estimate =>
              (repeatEstimateMeasure (base.runEstimate oracle) repetitions).map
                fun tailValues =>
                  (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)) by
          funext estimate
          exact hinnerLaw estimate]
        exact measurable_measure_map_param _ (measurable_finCons repetitions)
      rw [repeatOracleProgram]
      constructor
      · exact hbase.bind hinnerStrong htailRun
      · rw [MembershipOracleProgram.runEstimate_bind oracle base _ hbase
            hinnerStrong htailRun]
        rw [show (fun estimate =>
            (tail.bind fun tailValues => .pure
              (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)).runEstimate oracle) =
            (fun estimate =>
              (repeatEstimateMeasure (base.runEstimate oracle) repetitions).map
                fun tailValues =>
                  (Fin.cons estimate tailValues : Fin (repetitions + 1) → ℝ)) by
          funext estimate
          exact hinnerLaw estimate]
        rfl

theorem amplifyOracleProgram_semantics
    (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
    (q : VolumeParams) (oracle : AmbientSpace q.n → Bool)
    (hbase : (base q).StronglyMeasurable oracle) :
    (amplifyOracleProgram base q).StronglyMeasurable oracle ∧
      (amplifyOracleProgram base q).runEstimate oracle =
        (repeatEstimateMeasure ((base q).runEstimate oracle)
          (confidenceRepetitions q)).map Arlib.Probability.medianOf := by
  have hrepeat := repeatOracleProgram_semantics (base q) oracle hbase
    (confidenceRepetitions q)
  have hpureStrong : ∀ estimates : Fin (confidenceRepetitions q) → ℝ,
      (MembershipOracleProgram.pure
        (Arlib.Probability.medianOf estimates)).StronglyMeasurable oracle :=
    fun _ => trivial
  have hpureRun : Measurable fun estimates : Fin (confidenceRepetitions q) → ℝ =>
      (MembershipOracleProgram.pure
        (Arlib.Probability.medianOf estimates)).runEstimate oracle := by
    simp only [MembershipOracleProgram.runEstimate]
    exact Measure.measurable_dirac.comp (measurable_medianOf _)
  unfold amplifyOracleProgram
  constructor
  · exact hrepeat.1.bind hpureStrong hpureRun
  · rw [MembershipOracleProgram.runEstimate_bind oracle _ _ hrepeat.1
      hpureStrong hpureRun]
    rw [hrepeat.2]
    exact Measure.bind_dirac_eq_map _ (measurable_medianOf _)

/-- Median amplification for any measurable, query-bounded base oracle program. -/
theorem oracleProgram_proof_amplification :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (base : (q : VolumeParams) → MembershipOracleProgram q.n ℝ)
          (q : VolumeParams) (I : VolumeInput q.n)
          (oracle : MembershipOracle I),
          3 / 4 ≤
              outcomeProbability
                (volumeAlgorithmLaw base q I oracle) (accurateOutcome q I) →
            (base q).StronglyMeasurable oracle.query →
            (∃ calls, (base q).QueryBound calls ∧
              calls ≤ Nat.ceil (C₀ * volumeBaseComplexityRate q)) →
              1 - q.p ≤
                  outcomeProbability
                    (volumeAlgorithmLaw (amplifyOracleProgram base) q I oracle)
                    (accurateOutcome q I) ∧
                ∃ calls,
                  (amplifyOracleProgram base q).QueryBound calls ∧
                  calls ≤ Nat.ceil (C * volumeComplexityRate q) := by
  intro C₀ hC₀
  let C : ℝ := 9 * (C₀ + 1)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro base q I oracle hprob hmeas hcost
  let μ : Measure ℝ := (base q).runEstimate oracle.query
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
        (volumeAlgorithmLaw (amplifyOracleProgram base) q I oracle)
        (accurateOutcome q I) := by
    have hsem := amplifyOracleProgram_semantics base q oracle.query hmeas
    rw [outcomeProbability_eq_measure]
    unfold volumeAlgorithmLaw
    rw [hsem.2]
    rw [Measure.map_apply (measurable_medianOf _) (accurateOutcome_measurable q I)]
    exact le_trans (by linarith) hmedian
  refine ⟨haccuracy, ?_⟩
  obtain ⟨B, hBprogram, hB⟩ := hcost
  refine ⟨m * B, ?_, ?_⟩
  · simpa [m] using amplifyOracleProgram_queryBound base q hBprogram
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
