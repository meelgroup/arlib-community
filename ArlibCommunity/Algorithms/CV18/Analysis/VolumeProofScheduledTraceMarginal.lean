/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledLossPreservingTrace

/-! # Live/dead retained marginals of the scheduled loss trace -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set

def scheduledBalancedTraceLiveSet (n : ℕ) :
    Set (ScheduledBalancedCoolingTrace n) := {trace | trace.2 = true}

def scheduledBalancedTraceDeadSet (n : ℕ) :
    Set (ScheduledBalancedCoolingTrace n) := {trace | trace.2 = false}

theorem measurableSet_scheduledBalancedTraceLiveSet :
    MeasurableSet (scheduledBalancedTraceLiveSet n) :=
  (measurable_snd : Measurable fun trace :
    ScheduledBalancedCoolingTrace n => trace.2) (measurableSet_singleton true)

theorem measurableSet_scheduledBalancedTraceDeadSet :
    MeasurableSet (scheduledBalancedTraceDeadSet n) :=
  (measurable_snd : Measurable fun trace :
    ScheduledBalancedCoolingTrace n => trace.2) (measurableSet_singleton false)

theorem scheduledBalancedTraceDeadSet_eq_compl :
    scheduledBalancedTraceDeadSet n =
      (scheduledBalancedTraceLiveSet n)ᶜ := by
  ext trace
  rcases trace with ⟨history, live⟩
  cases live <;> simp [scheduledBalancedTraceDeadSet,
    scheduledBalancedTraceLiveSet]

def scheduledBalancedTraceRetainedState
    (trace : ScheduledBalancedCoolingTrace n) : AmbientSpace n :=
  trace.1.2.2.2

theorem measurable_scheduledBalancedTraceRetainedState :
    Measurable (scheduledBalancedTraceRetainedState (n := n)) := by
  unfold scheduledBalancedTraceRetainedState
  exact measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_fst))

noncomputable def scheduledBalancedTraceStateLaw
    (law : Measure (ScheduledBalancedCoolingTrace n))
    (transform : AmbientSpace n → AmbientSpace n) : Measure (AmbientSpace n) :=
  law.map (transform ∘ scheduledBalancedTraceRetainedState)

noncomputable def scheduledBalancedTraceLiveStateLaw
    (law : Measure (ScheduledBalancedCoolingTrace n))
    (transform : AmbientSpace n → AmbientSpace n) : Measure (AmbientSpace n) :=
  (law.restrict (scheduledBalancedTraceLiveSet n)).map
    (transform ∘ scheduledBalancedTraceRetainedState)

noncomputable def scheduledBalancedTraceDeadStateLaw
    (law : Measure (ScheduledBalancedCoolingTrace n))
    (transform : AmbientSpace n → AmbientSpace n) : Measure (AmbientSpace n) :=
  (law.restrict (scheduledBalancedTraceDeadSet n)).map
    (transform ∘ scheduledBalancedTraceRetainedState)

/-- The retained-state marginal splits exactly into its live and dead
submeasures, for either the identity map or the phase rescaling map. -/
theorem scheduledBalancedTraceStateLaw_eq_live_add_dead
    (law : Measure (ScheduledBalancedCoolingTrace n))
    (transform : AmbientSpace n → AmbientSpace n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceStateLaw law transform =
      scheduledBalancedTraceLiveStateLaw law transform +
        scheduledBalancedTraceDeadStateLaw law transform := by
  let f := transform ∘ scheduledBalancedTraceRetainedState
  have hf : Measurable f :=
    htransform.comp measurable_scheduledBalancedTraceRetainedState
  rw [scheduledBalancedTraceStateLaw,
    scheduledBalancedTraceLiveStateLaw,
    scheduledBalancedTraceDeadStateLaw, ← Measure.map_add _ _ hf]
  congr 1
  rw [scheduledBalancedTraceDeadSet_eq_compl,
    Measure.restrict_add_restrict_compl
      measurableSet_scheduledBalancedTraceLiveSet]

theorem scheduledBalancedTraceDeadStateLaw_apply_univ
    (law : Measure (ScheduledBalancedCoolingTrace n))
    (transform : AmbientSpace n → AmbientSpace n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceDeadStateLaw law transform Set.univ =
      law (scheduledBalancedTraceDeadSet n) := by
  rw [scheduledBalancedTraceDeadStateLaw,
    Measure.map_apply
      (htransform.comp measurable_scheduledBalancedTraceRetainedState)
      MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ]
  simp

/-- Dead trace mass is exactly the failure atom of the public optional
projection. -/
theorem scheduledBalancedTraceDeadStateLaw_mass_eq_project_none
    (law : Measure (ScheduledBalancedCoolingTrace n))
    (transform : AmbientSpace n → AmbientSpace n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceDeadStateLaw law transform Set.univ =
      (law.map scheduledBalancedCoolingTraceProject) {none} := by
  rw [scheduledBalancedTraceDeadStateLaw_apply_univ law transform htransform,
    Measure.map_apply measurable_scheduledBalancedCoolingTraceProject
      measurableSet_option_none]
  congr 1
  ext trace
  rcases trace with ⟨history, live⟩
  cases live <;> simp [scheduledBalancedTraceDeadSet,
    scheduledBalancedCoolingTraceProject]

/-- Applied to the concrete forward trace, the dead retained marginal is
exactly the failure probability already visible in the chronological
optional-history law. -/
theorem figureOneFinalScheduledTraceDeadStateLaw_mass_eq_history_none
    (q : VolumeParams) (I : VolumeInput q.n) (phases : ℕ)
    (transform : AmbientSpace q.n → AmbientSpace q.n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceDeadStateLaw
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I phases) transform Set.univ =
      scheduledBalancedForwardHistoryLaw
        figureOneFinalScheduledBalancedParameters q I phases {none} := by
  rw [scheduledBalancedTraceDeadStateLaw_mass_eq_project_none
    _ transform htransform,
    map_scheduledBalancedForwardTraceLaw_project]

#print axioms scheduledBalancedTraceStateLaw_eq_live_add_dead
#print axioms scheduledBalancedTraceDeadStateLaw_mass_eq_project_none
#print axioms figureOneFinalScheduledTraceDeadStateLaw_mass_eq_history_none

end ArlibCommunity.Algorithms.CV18
