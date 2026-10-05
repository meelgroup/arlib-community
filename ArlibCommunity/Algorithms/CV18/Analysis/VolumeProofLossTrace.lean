import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryProgram

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- Forget the loss-preserving history carried by a dead trace. -/
def lossTraceProject {H : Type*} (state : H × Bool) : Option H :=
  if state.2 then some state.1 else none

theorem measurable_lossTraceProject {H : Type*} [MeasurableSpace H] :
    Measurable (lossTraceProject : H × Bool → Option H) := by
  unfold lossTraceProject
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_snd measurable_const
  · exact measurable_some.comp measurable_fst
  · exact measurable_const

/-- Lift an optional transition result to a trace, retaining an explicitly
chosen history on failure. -/
def lossTraceResult {H : Type*} (onFailure : H → H) (current : H) :
    Option H → H × Bool
  | none => (onFailure current, false)
  | some next => (next, true)

theorem measurable_lossTraceResult {H : Type*} [MeasurableSpace H]
    (onFailure : H → H) (honFailure : Measurable onFailure) :
    Measurable fun value : H × Option H =>
      lossTraceResult onFailure value.1 value.2 := by
  have hnone : Measurable fun current : H => (onFailure current, false) :=
    honFailure.prodMk measurable_const
  have hsome : Measurable fun value : H × H => (value.2, true) :=
    measurable_snd.prodMk measurable_const
  convert Measurable.optionElimParam hnone hsome using 1
  funext value
  cases value.2 <;> rfl

noncomputable def lossTraceKernel {H : Type*} [MeasurableSpace H]
    (K : H → Measure (Option H)) (onFailure : H → H) :
    H × Bool → Measure (H × Bool)
  | (current, true) =>
      (K current).map (lossTraceResult onFailure current)
  | (current, false) => Measure.dirac (onFailure current, false)

noncomputable def absorbingOptionKernel {H : Type*} [MeasurableSpace H]
    (K : H → Measure (Option H)) : Option H → Measure (Option H)
  | none => Measure.dirac none
  | some current => K current

theorem lossTraceProject_result {H : Type*} (onFailure : H → H)
    (current : H) (result : Option H) :
    lossTraceProject (lossTraceResult onFailure current result) = result := by
  cases result <;> rfl

/-- One lifted trace step projects exactly to the original absorbing optional
step, independently of which history is retained on failure. -/
theorem lossTraceKernel_map_project {H : Type*} [MeasurableSpace H]
    (K : H → Measure (Option H)) (_hK : Measurable K)
    (onFailure : H → H) (honFailure : Measurable onFailure)
    (state : H × Bool) :
    (lossTraceKernel K onFailure state).map lossTraceProject =
      absorbingOptionKernel K (lossTraceProject state) := by
  rcases state with ⟨current, live⟩
  cases live with
  | false =>
      simp [lossTraceKernel, lossTraceProject, absorbingOptionKernel,
        measurable_lossTraceProject]
  | true =>
      simp only [lossTraceKernel, lossTraceProject, if_true,
        absorbingOptionKernel]
      have hresult : Measurable (lossTraceResult onFailure current) :=
        (measurable_lossTraceResult onFailure honFailure).comp
          (measurable_const.prodMk measurable_id)
      rw [Measure.map_map measurable_lossTraceProject hresult]
      rw [show lossTraceProject ∘ lossTraceResult onFailure current = id by
        funext result
        exact lossTraceProject_result onFailure current result]
      exact Measure.map_id

theorem lossTraceKernel_measurable_and_probability
    {H : Type*} [MeasurableSpace H]
    (K : H → Measure (Option H)) (hK : Measurable K)
    (hKprob : ∀ current, IsProbabilityMeasure (K current))
    (onFailure : H → H) (honFailure : Measurable onFailure) :
    Measurable (lossTraceKernel K onFailure) ∧
      ∀ state, IsProbabilityMeasure (lossTraceKernel K onFailure state) := by
  constructor
  · have hlive : Measurable fun current : H =>
        (K current).map (lossTraceResult onFailure current) := by
      exact measurable_measure_map_param_variable hK hKprob
        (measurable_lossTraceResult onFailure honFailure)
    have hdead : Measurable fun current : H =>
        Measure.dirac (onFailure current, false) :=
      Measure.measurable_dirac.comp (honFailure.prodMk measurable_const)
    rw [show lossTraceKernel K onFailure = fun state =>
        if state.2 then
          (K state.1).map (lossTraceResult onFailure state.1)
        else Measure.dirac (onFailure state.1, false) by
      funext state
      rcases state with ⟨current, live⟩
      cases live <;> rfl]
    apply Measurable.ite
    · exact measurableSet_eq_fun measurable_snd measurable_const
    · exact hlive.comp measurable_fst
    · exact hdead.comp measurable_fst
  · intro state
    rcases state with ⟨current, live⟩
    cases live with
    | false =>
        unfold lossTraceKernel
        infer_instance
    | true =>
        unfold lossTraceKernel
        let _ : IsProbabilityMeasure (K current) := hKprob current
        exact Measure.isProbabilityMeasure_map
          ((measurable_lossTraceResult onFailure honFailure).comp
            (measurable_const.prodMk measurable_id)).aemeasurable

#print axioms lossTraceKernel_map_project
#print axioms lossTraceKernel_measurable_and_probability

end ArlibCommunity.Algorithms.CV18
