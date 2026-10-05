/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledExecutableHistory

/-! # Exact joint history law of scheduled Gaussian cooling -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable def scheduledExecutableCoolingHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    List ℝ → AmbientSpace q.n →
      Measure (Option (BalancedCoolingHistory q.n))
  | [], point => Measure.dirac (some ((fun _ => 0), 0, 1, point))
  | [_], point => Measure.dirac (some ((fun _ => 0), 0, 1, point))
  | sigma2 :: tau2 :: rest, point =>
      (scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2 point).bind fun phase =>
        match phase with
        | none => Measure.dirac none
        | some (ratio, nextPoint) =>
            (scheduledExecutableCoolingHistoryLaw parameters q I (tau2 :: rest) nextPoint).map
              (balancedCoolingHistoryCons ratio)
termination_by variances => variances.length

/-- The scheduled cooling history is a measurable probability kernel of its
initial target-space point. -/
theorem scheduledExecutableCoolingHistoryLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ∀ variances : List ℝ,
      (∀ sigma2 ∈ variances, 0 < sigma2) →
      Measurable (scheduledExecutableCoolingHistoryLaw parameters q I variances) ∧
      ∀ point, IsProbabilityMeasure
        (scheduledExecutableCoolingHistoryLaw parameters q I variances point) := by
  intro variances
  induction variances with
  | nil =>
      intro _
      constructor
      · rw [show scheduledExecutableCoolingHistoryLaw parameters q I [] =
            fun point => Measure.dirac
              (some ((fun _ : ℕ => (0 : ℝ)), 0, 1, point)) by
          funext point
          rw [scheduledExecutableCoolingHistoryLaw]]
        exact Measure.measurable_dirac.comp <| measurable_some.comp <|
          measurable_const.prodMk <| measurable_const.prodMk <|
            measurable_const.prodMk measurable_id
      · intro point
        rw [scheduledExecutableCoolingHistoryLaw]
        infer_instance
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro _
          constructor
          · rw [show scheduledExecutableCoolingHistoryLaw parameters q I [sigma2] =
                fun point => Measure.dirac
                  (some ((fun _ : ℕ => (0 : ℝ)), 0, 1, point)) by
              funext point
              rw [scheduledExecutableCoolingHistoryLaw]]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_const.prodMk <| measurable_const.prodMk <|
                measurable_const.prodMk measurable_id
          · intro point
            rw [scheduledExecutableCoolingHistoryLaw]
            infer_instance
      | cons tau2 rest =>
          intro hpositive
          have hsigma2 : 0 < sigma2 := hpositive sigma2 (by simp)
          have htailPositive : ∀ s ∈ tau2 :: rest, 0 < s := by
            intro s hs
            exact hpositive s (List.mem_cons_of_mem sigma2 hs)
          have htail := ih htailPositive
          have hphase := scheduledBalancedCoolingRatioLaw_measurable_and_probability
            parameters q I hsigma2 tau2
          let continuation : Option (ℝ × AmbientSpace q.n) →
              Measure (Option (BalancedCoolingHistory q.n)) := fun phase =>
            match phase with
            | none => Measure.dirac none
            | some (ratio, nextPoint) =>
                (scheduledExecutableCoolingHistoryLaw parameters q I
                  (tau2 :: rest) nextPoint).map
                    (balancedCoolingHistoryCons ratio)
          have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
              (scheduledExecutableCoolingHistoryLaw parameters q I
                (tau2 :: rest) value.2).map
                  (balancedCoolingHistoryCons value.1) := by
            apply measurable_measure_map_param_variable
              (htail.1.comp measurable_snd) (fun value => htail.2 value.2)
            exact measurable_balancedCoolingHistoryCons.comp <|
              (measurable_fst.comp measurable_fst).prodMk measurable_snd
          have hcontinuation : Measurable continuation := by
            dsimp only [continuation]
            convert Measurable.optionElim
              (Measure.dirac (none : Option (BalancedCoolingHistory q.n)))
                hsome using 1
            funext phase
            cases phase <;> rfl
          have hcontinuationProb : ∀ phase,
              IsProbabilityMeasure (continuation phase) := by
            intro phase
            cases phase with
            | none =>
                dsimp only [continuation]
                infer_instance
            | some value =>
                dsimp only [continuation]
                let _ : IsProbabilityMeasure
                    (scheduledExecutableCoolingHistoryLaw parameters q I
                      (tau2 :: rest) value.2) := htail.2 value.2
                exact Measure.isProbabilityMeasure_map <|
                  (measurable_balancedCoolingHistoryCons (n := q.n)).comp
                    (measurable_const.prodMk measurable_id) |>.aemeasurable
          have hlaw : scheduledExecutableCoolingHistoryLaw parameters q I
                (sigma2 :: tau2 :: rest) =
              fun point =>
                (scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2 point).bind
                  continuation := by
            funext point
            simp only [scheduledExecutableCoolingHistoryLaw]
            apply Measure.bind_congr_right
            filter_upwards with phase
            cases phase <;> rfl
          constructor
          · rw [hlaw]
            exact (Measure.measurable_bind' hcontinuation).comp hphase.1
          · intro point
            rw [congrFun hlaw point]
            let _ : IsProbabilityMeasure
                (scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2 point) :=
              hphase.2 point
            exact MeasureTheory.isProbabilityMeasure_bind
              hcontinuation.aemeasurable
                (ae_of_all _ hcontinuationProb)

/-- The executable balanced cooling product is a measurable kernel, with no
extra analytic hypothesis beyond positivity of the variances. -/
theorem scheduledExecutableCoolingProduct_measurable_and_strong
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ variances : List ℝ,
      (∀ sigma2 ∈ variances, 0 < sigma2) →
      Measurable (fun point =>
        (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q variances point).runEstimate
          oracle.query) ∧
      ∀ point,
        (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q variances point).StronglyMeasurable
          oracle.query := by
  intro variances
  induction variances with
  | nil =>
      intro _
      constructor
      · simp only [coolingProduct, MembershipOracleProgram.runEstimate]
        exact Measure.measurable_dirac.comp <| measurable_some.comp <|
          measurable_const.prodMk measurable_id
      · intro point
        simpa [coolingProduct] using
          (show (MembershipOracleProgram.pure (some (1, point)) :
            MembershipOracleProgram q.n
              (Option (ℝ × AmbientSpace q.n))).StronglyMeasurable
                oracle.query from trivial)
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro _
          constructor
          · simp only [coolingProduct, MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp <| measurable_some.comp <|
              measurable_const.prodMk measurable_id
          · intro point
            simpa [coolingProduct] using
              (show (MembershipOracleProgram.pure (some (1, point)) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).StronglyMeasurable
                    oracle.query from trivial)
      | cons tau2 rest =>
          intro hpositive
          have hsigma2 : 0 < sigma2 := hpositive sigma2 (by simp)
          have htailPositive : ∀ s ∈ tau2 :: rest, 0 < s := by
            intro s hs
            exact hpositive s (List.mem_cons_of_mem sigma2 hs)
          have htail := ih htailPositive
          have hratio :=
            scheduledBalancedCoolingRatioEstimate_measurable_strong_and_law
              parameters q I oracle hsigma2 tau2
          let phaseProgram : Option (ℝ × AmbientSpace q.n) →
              MembershipOracleProgram q.n
                (Option (ℝ × AmbientSpace q.n)) := fun phase =>
            match phase with
            | none => .pure none
            | some (ratio, nextPoint) =>
                (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (tau2 :: rest) nextPoint).bind fun result =>
                    .pure <| match result with
                    | none => none
                    | some (product, lastPoint) =>
                        some (ratio * product, lastPoint)
          have htailOutput : ∀ ratio, Measurable fun result :
              Option (ℝ × AmbientSpace q.n) =>
              (.pure (match result with
                | none => none
                | some (product, lastPoint) =>
                    some (ratio * product, lastPoint)) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).runEstimate oracle.query := by
            intro ratio
            simp only [MembershipOracleProgram.runEstimate]
            apply Measure.measurable_dirac.comp
            have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
                some (ratio * value.1, value.2) :=
              measurable_some.comp <|
                (measurable_const.mul measurable_fst).prodMk measurable_snd
            convert Measurable.optionElim
              (none : Option (ℝ × AmbientSpace q.n)) hsome using 1
            funext result
            cases result with
            | none => rfl
            | some value => cases value; rfl
          have hphaseStrong : ∀ phase,
              (phaseProgram phase).StronglyMeasurable oracle.query := by
            intro phase
            cases phase with
            | none => trivial
            | some value =>
                exact (htail.2 value.2).bind (fun _ => by trivial)
                  (htailOutput value.1)
          have hsomeRun : Measurable fun value : ℝ × AmbientSpace q.n =>
              (phaseProgram (some value)).runEstimate oracle.query := by
            have hsource : Measurable fun value : ℝ × AmbientSpace q.n =>
                (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query :=
              htail.1.comp measurable_snd
            have hprob : ∀ value : ℝ × AmbientSpace q.n,
                IsProbabilityMeasure
                  ((coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                    (tau2 :: rest) value.2).runEstimate oracle.query) :=
              fun value =>
                MembershipOracleProgram.runEstimate_isProbabilityMeasure
                  oracle.query _ (htail.2 value.2).estimateMeasurable
            have htransform : Measurable fun p :
                (ℝ × AmbientSpace q.n) ×
                  Option (ℝ × AmbientSpace q.n) =>
                match p.2 with
                | none => none
                | some (product, lastPoint) =>
                    some (p.1.1 * product, lastPoint) := by
              have hnone : Measurable fun _ : ℝ × AmbientSpace q.n =>
                  (none : Option (ℝ × AmbientSpace q.n)) := measurable_const
              have hsome : Measurable fun p :
                  (ℝ × AmbientSpace q.n) × (ℝ × AmbientSpace q.n) =>
                  some (p.1.1 * p.2.1, p.2.2) :=
                measurable_some.comp <|
                  ((measurable_fst.comp measurable_fst).mul
                    (measurable_fst.comp measurable_snd)).prodMk
                      (measurable_snd.comp measurable_snd)
              convert Measurable.optionCases
                ((0 : ℝ), (0 : AmbientSpace q.n)) hnone hsome using 1
              funext p
              cases p.2 with
              | none => rfl
              | some value => cases value; rfl
            have hbind : Measurable fun value : ℝ × AmbientSpace q.n =>
                ((coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query).bind
                    fun result => Measure.dirac <| match result with
                    | none => none
                    | some (product, lastPoint) =>
                        some (value.1 * product, lastPoint) :=
              measurable_measure_bind_param_variable hsource hprob
                (Measure.measurable_dirac.comp htransform)
            rw [show (fun value : ℝ × AmbientSpace q.n =>
                (phaseProgram (some value)).runEstimate oracle.query) =
              (fun value =>
                ((coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query).bind
                    fun result => Measure.dirac <| match result with
                    | none => none
                    | some (product, lastPoint) =>
                        some (value.1 * product, lastPoint)) by
              funext value
              unfold phaseProgram
              exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
                (htail.2 value.2) (fun _ => by trivial)
                  (htailOutput value.1)]
            exact hbind
          have hphaseRun : Measurable fun phase =>
              (phaseProgram phase).runEstimate oracle.query := by
            convert Measurable.optionElim
              (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
                hsomeRun using 1
            funext phase
            cases phase <;> rfl
          have hcooling : ∀ point,
              coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (sigma2 :: tau2 :: rest) point =
                (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind
                  phaseProgram := by
            intro point
            rw [coolingProduct]
            change (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind _ = _
            congr 1
            funext phase
            cases phase with
            | none => rfl
            | some value =>
                cases value with
                | mk ratio nextPoint =>
                    unfold phaseProgram
                    simp only
                    congr 1
                    funext result
                    cases result with
                    | none => rfl
                    | some value => cases value; rfl
          have hrun : (fun point =>
              (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                (sigma2 :: tau2 :: rest) point).runEstimate oracle.query) =
              fun point =>
                ((scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 point).runEstimate
                  oracle.query).bind fun phase =>
                    (phaseProgram phase).runEstimate oracle.query := by
            funext point
            rw [hcooling point]
            exact MembershipOracleProgram.runEstimate_bind oracle.query _ _
              (hratio.2.1 point) hphaseStrong hphaseRun
          constructor
          · rw [hrun]
            exact (Measure.measurable_bind' hphaseRun).comp hratio.1
          · intro point
            rw [hcooling point]
            exact (hratio.2.1 point).bind hphaseStrong hphaseRun

/-- The executable continuation is exactly the output map of the one joint
history law.  In particular, the accumulated product and retained point are
not merely distributionally postulated phase by phase. -/
theorem scheduledExecutableCoolingProduct_runEstimate_eq_history_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I) :
    ∀ variances : List ℝ,
      (∀ sigma2 ∈ variances, 0 < sigma2) →
      ∀ point,
        (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q variances point).runEstimate
            oracle.query =
          (scheduledExecutableCoolingHistoryLaw parameters q I variances point).map
            balancedCoolingHistoryOutput := by
  intro variances
  induction variances with
  | nil =>
      intro _ point
      simp only [coolingProduct, MembershipOracleProgram.runEstimate]
      rw [scheduledExecutableCoolingHistoryLaw, Measure.map_dirac'
        measurable_balancedCoolingHistoryOutput]
      rfl
  | cons sigma2 tail ih =>
      cases tail with
      | nil =>
          intro _ point
          simp only [coolingProduct, MembershipOracleProgram.runEstimate]
          rw [scheduledExecutableCoolingHistoryLaw, Measure.map_dirac'
            measurable_balancedCoolingHistoryOutput]
          rfl
      | cons tau2 rest =>
          intro hpositive point
          have hsigma2 : 0 < sigma2 := hpositive sigma2 (by simp)
          have htailPositive : ∀ s ∈ tau2 :: rest, 0 < s := by
            intro s hs
            exact hpositive s (List.mem_cons_of_mem sigma2 hs)
          have htailMS := scheduledExecutableCoolingProduct_measurable_and_strong
            parameters q I oracle (tau2 :: rest) htailPositive
          have htailLaw := scheduledExecutableCoolingHistoryLaw_measurable_and_probability
            parameters q I (tau2 :: rest) htailPositive
          have hratio :=
            scheduledBalancedCoolingRatioEstimate_measurable_strong_and_law
              parameters q I oracle hsigma2 tau2
          let phaseProgram : Option (ℝ × AmbientSpace q.n) →
              MembershipOracleProgram q.n
                (Option (ℝ × AmbientSpace q.n)) := fun phase =>
            match phase with
            | none => .pure none
            | some (ratio, nextPoint) =>
                (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (tau2 :: rest) nextPoint).bind fun result =>
                    .pure (balancedCoolingProductCons ratio result)
          have hproductCons (ratio : ℝ) :
              Measurable (balancedCoolingProductCons
                (n := q.n) ratio) :=
            measurable_balancedCoolingProductCons.comp
              (measurable_const.prodMk measurable_id)
          have hpureRun (ratio : ℝ) : Measurable fun result :
              Option (ℝ × AmbientSpace q.n) =>
              (.pure (balancedCoolingProductCons ratio result) :
                MembershipOracleProgram q.n
                  (Option (ℝ × AmbientSpace q.n))).runEstimate oracle.query := by
            simp only [MembershipOracleProgram.runEstimate]
            exact Measure.measurable_dirac.comp (hproductCons ratio)
          have hphaseStrong : ∀ phase,
              (phaseProgram phase).StronglyMeasurable oracle.query := by
            intro phase
            cases phase with
            | none => trivial
            | some value =>
                exact (htailMS.2 value.2).bind (fun _ => by trivial)
                  (hpureRun value.1)
          have hsomeLaw : ∀ value : ℝ × AmbientSpace q.n,
              (phaseProgram (some value)).runEstimate oracle.query =
                ((coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query).map
                    (balancedCoolingProductCons value.1) := by
            intro value
            unfold phaseProgram
            rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
              (htailMS.2 value.2) (fun _ => by trivial) (hpureRun value.1)]
            exact Measure.bind_dirac_eq_map _ (hproductCons value.1)
          have hsomeRun : Measurable fun value : ℝ × AmbientSpace q.n =>
              (phaseProgram (some value)).runEstimate oracle.query := by
            rw [show (fun value : ℝ × AmbientSpace q.n =>
                (phaseProgram (some value)).runEstimate oracle.query) =
              fun value =>
                ((coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (tau2 :: rest) value.2).runEstimate oracle.query).map
                    (balancedCoolingProductCons value.1) by
              funext value
              exact hsomeLaw value]
            apply measurable_measure_map_param_variable
              (htailMS.1.comp measurable_snd)
            · intro value
              exact MembershipOracleProgram.runEstimate_isProbabilityMeasure
                oracle.query _ (htailMS.2 value.2).estimateMeasurable
            · exact measurable_balancedCoolingProductCons.comp <|
                (measurable_fst.comp measurable_fst).prodMk measurable_snd
          have hphaseRun : Measurable fun phase =>
              (phaseProgram phase).runEstimate oracle.query := by
            convert Measurable.optionElim
              (Measure.dirac (none : Option (ℝ × AmbientSpace q.n)))
                hsomeRun using 1
            funext phase
            cases phase <;> rfl
          have hcooling :
              coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                  (sigma2 :: tau2 :: rest) point =
                (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind
                  phaseProgram := by
            rw [coolingProduct]
            change (scheduledBalancedCoolingRatioEstimate parameters q sigma2 tau2 point).bind _ = _
            congr 1
            funext phase
            cases phase with
            | none => rfl
            | some value =>
                rcases value with ⟨ratio, nextPoint⟩
                change
                  (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                    (tau2 :: rest) nextPoint).bind (fun result =>
                      .pure <| match result with
                      | some (product, lastPoint) =>
                          some (ratio * product, lastPoint)
                      | none => none) =
                  (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
                    (tau2 :: rest) nextPoint).bind (fun result =>
                      .pure (balancedCoolingProductCons ratio result))
                congr 1
                funext result
                cases result <;> rfl
          have hcontinuation : Measurable fun phase :
              Option (ℝ × AmbientSpace q.n) =>
              match phase with
              | none => Measure.dirac
                  (none : Option (BalancedCoolingHistory q.n))
              | some (ratio, nextPoint) =>
                  (scheduledExecutableCoolingHistoryLaw parameters q I
                    (tau2 :: rest) nextPoint).map
                      (balancedCoolingHistoryCons ratio) := by
            have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
                (scheduledExecutableCoolingHistoryLaw parameters q I
                  (tau2 :: rest) value.2).map
                    (balancedCoolingHistoryCons value.1) := by
              apply measurable_measure_map_param_variable
                (htailLaw.1.comp measurable_snd)
                (fun value => htailLaw.2 value.2)
              exact measurable_balancedCoolingHistoryCons.comp <|
                (measurable_fst.comp measurable_fst).prodMk measurable_snd
            convert Measurable.optionElim
              (Measure.dirac (none : Option (BalancedCoolingHistory q.n)))
                hsome using 1
            funext phase
            cases phase <;> rfl
          rw [hcooling]
          rw [MembershipOracleProgram.runEstimate_bind oracle.query _ _
            (hratio.2.1 point) hphaseStrong hphaseRun]
          rw [hratio.2.2 point]
          rw [scheduledExecutableCoolingHistoryLaw]
          rw [map_bind_eq_bind_map_of_measurable _ hcontinuation
            measurable_balancedCoolingHistoryOutput]
          apply Measure.bind_congr_right
          filter_upwards with phase
          cases phase with
          | none =>
              simp only [phaseProgram, MembershipOracleProgram.runEstimate]
              rw [Measure.map_dirac' measurable_balancedCoolingHistoryOutput]
              rfl
          | some value =>
              rw [hsomeLaw value, ih htailPositive value.2]
              rw [Measure.map_map
                (hproductCons value.1)
                measurable_balancedCoolingHistoryOutput]
              let mu := scheduledExecutableCoolingHistoryLaw parameters q I
                (tau2 :: rest) value.2
              have hhistoryCons : Measurable
                  (balancedCoolingHistoryCons (n := q.n) value.1) :=
                measurable_balancedCoolingHistoryCons.comp
                  (measurable_const.prodMk measurable_id)
              calc
                Measure.map (balancedCoolingProductCons value.1 ∘
                    balancedCoolingHistoryOutput) mu =
                    Measure.map (balancedCoolingHistoryOutput ∘
                      balancedCoolingHistoryCons value.1) mu := by
                  apply Measure.map_congr
                  filter_upwards with history
                  exact (balancedCoolingHistoryOutput_cons
                    value.1 history).symm
                _ = (mu.map (balancedCoolingHistoryCons value.1)).map
                    balancedCoolingHistoryOutput :=
                  (Measure.map_map
                    (μ := mu)
                    (g := balancedCoolingHistoryOutput)
                    (f := balancedCoolingHistoryCons value.1)
                    measurable_balancedCoolingHistoryOutput
                    hhistoryCons).symm

/-- The single joint Gaussian-cooling history law for the explicit Figure-One
schedule.  Its sequence coordinates are the phase variables `W_j` consumed by
the dependent-product argument. -/
noncomputable def scheduledExecutableFigureOneCoolingHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (point : AmbientSpace q.n) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  scheduledExecutableCoolingHistoryLaw parameters q I
    (explicitVolumeCoolingSchedule q).variances point

theorem scheduledExecutableFigureOneCoolingHistoryLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    Measurable (scheduledExecutableFigureOneCoolingHistoryLaw parameters q I) ∧
    ∀ point, IsProbabilityMeasure
      (scheduledExecutableFigureOneCoolingHistoryLaw parameters q I point) := by
  exact scheduledExecutableCoolingHistoryLaw_measurable_and_probability parameters q I
    (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive

theorem scheduledExecutableFigureOneCoolingProduct_runEstimate_eq_history_map
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (point : AmbientSpace q.n) :
    (coolingProduct (scheduledBalancedCoolingPrimitives parameters) q
        (explicitVolumeCoolingSchedule q).variances point).runEstimate
          oracle.query =
      (scheduledExecutableFigureOneCoolingHistoryLaw parameters q I point).map
        balancedCoolingHistoryOutput := by
  exact scheduledExecutableCoolingProduct_runEstimate_eq_history_map parameters q I oracle
    (explicitVolumeCoolingSchedule q).variances
      (explicitVolumeCoolingSchedule q).positive point

#print axioms scheduledBalancedCoolingRatioEstimate_measurable_strong_and_law
#print axioms scheduledExecutableCoolingHistoryLaw_measurable_and_probability
#print axioms scheduledExecutableCoolingProduct_runEstimate_eq_history_map
#print axioms scheduledExecutableFigureOneCoolingProduct_runEstimate_eq_history_map

end ArlibCommunity.Algorithms.CV18
