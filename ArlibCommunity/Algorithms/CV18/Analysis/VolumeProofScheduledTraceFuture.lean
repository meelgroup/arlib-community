/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceTransport
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly

/-! # Preservation of completed CV18 coordinates by later phases -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- A later chronological append preserves an already completed nonnegative
phase variable. -/
theorem scheduledBalancedTracePhaseVariable_append_eq
    (q : VolumeParams) {m j : ℕ}
    {trace : ScheduledBalancedCoolingTrace q.n}
    (hvalid : ScheduledBalancedCoolingTraceValid m trace)
    (hmphase : m ≤ figureOneDependentPhaseCount q)
    (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (result : Option (ℝ × AmbientSpace q.n)) :
    scheduledBalancedTracePhaseVariable q j
        (scheduledBalancedCoolingTraceAppend trace result) =
      scheduledBalancedTracePhaseVariable q j trace := by
  unfold scheduledBalancedTracePhaseVariable
  rw [scheduledBalancedTraceChronologicalPhaseVariable_append_eq q hvalid
    hmphase hj1 hjm result]

/-- The first (coordinatewise) CV18 truncation is likewise preserved. -/
theorem scheduledFigureOneTraceTruncatedPhase_append_eq
    (q : VolumeParams) (I : VolumeInput q.n) {m j : ℕ}
    {trace : ScheduledBalancedCoolingTrace q.n}
    (hvalid : ScheduledBalancedCoolingTraceValid m trace)
    (hmphase : m ≤ figureOneDependentPhaseCount q)
    (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (result : Option (ℝ × AmbientSpace q.n)) :
    scheduledFigureOneTraceTruncatedPhase q I j
        (scheduledBalancedCoolingTraceAppend trace result) =
      scheduledFigureOneTraceTruncatedPhase q I j trace := by
  unfold scheduledFigureOneTraceTruncatedPhase dependentTruncatedPhase
  rw [scheduledBalancedTracePhaseVariable_append_eq q hvalid hmphase
    hj1 hjm result]

/-- The recursively truncated product through coordinate `i` is unchanged by
an append after all of those coordinates have already been completed. -/
theorem scheduledFigureOneTraceTruncatedProduct_append_eq
    (q : VolumeParams) (I : VolumeInput q.n) {m i : ℕ}
    {trace : ScheduledBalancedCoolingTrace q.n}
    (hvalid : ScheduledBalancedCoolingTraceValid m trace)
    (hmphase : m ≤ figureOneDependentPhaseCount q)
    (him : i ≤ m)
    (result : Option (ℝ × AmbientSpace q.n)) :
    dependentTruncatedProduct (figureOneDependentAlpha q)
        (scheduledFigureOneTraceTruncatedMean q I)
        (scheduledFigureOneTraceTruncatedPhase q I) i
        (scheduledBalancedCoolingTraceAppend trace result) =
      dependentTruncatedProduct (figureOneDependentAlpha q)
        (scheduledFigureOneTraceTruncatedMean q I)
        (scheduledFigureOneTraceTruncatedPhase q I) i trace := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [dependentTruncatedProduct_succ, dependentTruncatedProduct_succ,
        ih (by omega),
        scheduledFigureOneTraceTruncatedPhase_append_eq q I hvalid hmphase
          (by omega) (by omega) result]

/-- Once coordinate `i+1` has been appended, every later phase preserves the
joint pushforward law of the truncated prefix product and that coordinate.
This is the future-splicing step needed to state Lemma 7.17(c) on the final
loss-preserving trace rather than on an immediate one-phase pair law. -/
theorem map_pair_scheduledBalancedForwardTraceLaw_eq_prefix
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (i future : ℕ)
    (horizon : i + 1 + future ≤ figureOneDependentPhaseCount q) :
    let X := dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) i
    let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
    (scheduledBalancedForwardTraceLaw parameters q I (i + 1 + future)).map
        (fun trace => (X trace, Y trace)) =
      (scheduledBalancedForwardTraceLaw parameters q I (i + 1)).map
        (fun trace => (X trace, Y trace)) := by
  dsimp only
  let X := dependentTruncatedProduct (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledFigureOneTraceTruncatedPhase q I) i
  let Y := scheduledFigureOneTraceTruncatedPhase q I (i + 1)
  have hV : ∀ j, Measurable
      (scheduledFigureOneTraceTruncatedPhase q I j) := fun j =>
    (measurable_scheduledBalancedTracePhaseVariable q j).min measurable_const
  have hX : Measurable X :=
    measurable_dependentTruncatedProduct (figureOneDependentAlpha q)
      (scheduledFigureOneTraceTruncatedMean q I)
      (scheduledFigureOneTraceTruncatedPhase q I) hV i
  have hY : Measurable Y := hV (i + 1)
  induction future with
  | zero => rfl
  | succ future ih =>
      let m := i + 1 + future
      let law := scheduledBalancedForwardTraceLaw parameters q I m
      let K := scheduledBalancedTracePhaseKernel parameters q I m
      have hmphase : m ≤ figureOneDependentPhaseCount q := by
        dsimp only [m]
        omega
      have hK := scheduledBalancedTracePhaseKernel_measurable_and_probability
        parameters q I m
      have hpreserve : ∀ᵐ trace ∂law, ∀ᵐ next ∂K trace,
          X next = X trace ∧ Y next = Y trace := by
        filter_upwards [scheduledBalancedForwardTraceLaw_ae_valid
          parameters q I m] with trace hvalid
        unfold K scheduledBalancedTracePhaseKernel
        let append := scheduledBalancedCoolingTraceAppend trace
        have happend : Measurable append :=
          (measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
            (measurable_const.prodMk measurable_id)
        let good : Set (ScheduledBalancedCoolingTrace q.n) :=
          {next | X next = X trace ∧ Y next = Y trace}
        have hgood : MeasurableSet good :=
          (measurableSet_eq_fun hX measurable_const).inter
            (measurableSet_eq_fun hY measurable_const)
        apply (ae_map_iff happend.aemeasurable hgood).2
        filter_upwards with result
        constructor
        · exact scheduledFigureOneTraceTruncatedProduct_append_eq q I hvalid
            hmphase (by dsimp only [m]; omega) result
        · exact scheduledFigureOneTraceTruncatedPhase_append_eq q I hvalid
            hmphase (by omega) (by dsimp only [m]; omega) result
      have hstep :
          (law.bind K).map (fun trace => (X trace, Y trace)) =
            law.map (fun trace => (X trace, Y trace)) := by
        exact Measure.map_pair_bind_eq_of_ae_eq law K hK.1 hK.2
          X Y X Y hX hY hX hY hpreserve
      have hsuccLaw :
          scheduledBalancedForwardTraceLaw parameters q I
              (i + 1 + (future + 1)) = law.bind K := by
        rfl
      rw [hsuccLaw, hstep]
      exact ih (by omega)

#print axioms scheduledBalancedTracePhaseVariable_append_eq
#print axioms scheduledFigureOneTraceTruncatedPhase_append_eq
#print axioms scheduledFigureOneTraceTruncatedProduct_append_eq
#print axioms map_pair_scheduledBalancedForwardTraceLaw_eq_prefix

end ArlibCommunity.Algorithms.CV18
