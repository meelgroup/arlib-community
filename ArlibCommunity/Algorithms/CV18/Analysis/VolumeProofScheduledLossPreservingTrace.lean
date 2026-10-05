import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledHistoryNonnegative

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A chronological cooling trace retains completed phase coordinates after
the first executable failure.  The Boolean records whether execution is still
live.  Unlike `Option BalancedCoolingHistory`, this state does not erase the
past when a later phase fails. -/
abbrev ScheduledBalancedCoolingTrace (n : ℕ) :=
  BalancedCoolingHistory n × Bool

/-- Public executable projection: a dead trace is the ordinary failed
history. -/
def scheduledBalancedCoolingTraceProject :
    ScheduledBalancedCoolingTrace n → Option (BalancedCoolingHistory n)
  | (history, true) => some history
  | (_, false) => none

theorem measurable_scheduledBalancedCoolingTraceProject :
    Measurable (scheduledBalancedCoolingTraceProject (n := n)) := by
  have hlive : MeasurableSet
      {trace : ScheduledBalancedCoolingTrace n | trace.2 = true} :=
    (measurable_snd : Measurable fun trace :
      ScheduledBalancedCoolingTrace n => trace.2) (measurableSet_singleton true)
  convert Measurable.ite hlive
    (measurable_some.comp measurable_fst)
    (measurable_const : Measurable fun _ : ScheduledBalancedCoolingTrace n =>
      (none : Option (BalancedCoolingHistory n))) using 1
  funext trace
  rcases trace with ⟨history, live⟩
  cases live <;> rfl

/-- Append one phase coordinate directly to a nonoptional history. -/
noncomputable def balancedCoolingHistoryAppend
    (history : BalancedCoolingHistory n) (ratio : ℝ)
    (point : AmbientSpace n) : BalancedCoolingHistory n :=
  ((fun k => if k = history.2.1 then ratio else history.1 k),
    history.2.1 + 1, history.2.2.1 * ratio, point)

theorem measurable_balancedCoolingHistoryAppend :
    Measurable fun value :
        BalancedCoolingHistory n × (ℝ × AmbientSpace n) =>
      balancedCoolingHistoryAppend value.1 value.2.1 value.2.2 := by
  unfold balancedCoolingHistoryAppend
  have hsequence : Measurable fun value :
      BalancedCoolingHistory n × (ℝ × AmbientSpace n) =>
      fun k => if k = value.1.2.1 then value.2.1 else value.1.1 k := by
    refine measurable_pi_lambda _ fun k => ?_
    apply Measurable.ite
    · exact measurableSet_eq_fun measurable_const
        (measurable_fst.comp (measurable_snd.comp measurable_fst))
    · exact measurable_fst.comp measurable_snd
    · exact (measurable_pi_apply k).comp
        (measurable_fst.comp measurable_fst)
  exact hsequence.prodMk (by fun_prop)

@[simp] theorem balancedCoolingHistorySnocTerminal_some
    (history : BalancedCoolingHistory n) (ratio : ℝ)
    (point : AmbientSpace n) :
    balancedCoolingHistorySnocTerminal history (some (ratio, point)) =
      some (balancedCoolingHistoryAppend history ratio point) := rfl

/-- A live successful phase appends its observed ratio and retained point.  A
live failed phase appends zero, retains the last good point, and becomes dead.
A dead phase appends one and remains dead, so the accumulated product remains
zero while chronological length continues to advance. -/
noncomputable def scheduledBalancedCoolingTraceAppend
    (trace : ScheduledBalancedCoolingTrace n) :
    Option (ℝ × AmbientSpace n) → ScheduledBalancedCoolingTrace n
  | none =>
      if trace.2 then
        (balancedCoolingHistoryAppend trace.1 0 trace.1.2.2.2, false)
      else
        (balancedCoolingHistoryAppend trace.1 1 trace.1.2.2.2, false)
  | some result =>
      if trace.2 then
        (balancedCoolingHistoryAppend trace.1 result.1 result.2, true)
      else
        (balancedCoolingHistoryAppend trace.1 1 trace.1.2.2.2, false)

theorem measurable_scheduledBalancedCoolingTraceAppend :
    Measurable fun value : ScheduledBalancedCoolingTrace n ×
        Option (ℝ × AmbientSpace n) =>
      scheduledBalancedCoolingTraceAppend value.1 value.2 := by
  let live : Set (ScheduledBalancedCoolingTrace n) :=
    {trace | trace.2 = true}
  have hlive : MeasurableSet live :=
    (measurable_snd : Measurable fun trace :
      ScheduledBalancedCoolingTrace n => trace.2) (measurableSet_singleton true)
  have hkeep : Measurable fun trace : ScheduledBalancedCoolingTrace n =>
      trace.1.2.2.2 := by fun_prop
  have happendConst (ratio : ℝ) : Measurable fun trace :
      ScheduledBalancedCoolingTrace n =>
      balancedCoolingHistoryAppend trace.1 ratio trace.1.2.2.2 :=
    measurable_balancedCoolingHistoryAppend.comp <|
      measurable_fst.prodMk (measurable_const.prodMk hkeep)
  let noneValue : ScheduledBalancedCoolingTrace n →
      ScheduledBalancedCoolingTrace n := fun trace =>
    if trace.2 then
      (balancedCoolingHistoryAppend trace.1 0 trace.1.2.2.2, false)
    else
      (balancedCoolingHistoryAppend trace.1 1 trace.1.2.2.2, false)
  have hnone : Measurable noneValue := by
    dsimp only [noneValue]
    exact Measurable.ite hlive
      ((happendConst 0).prodMk measurable_const)
      ((happendConst 1).prodMk measurable_const)
  let someValue : ScheduledBalancedCoolingTrace n ×
      (ℝ × AmbientSpace n) → ScheduledBalancedCoolingTrace n := fun value =>
    if value.1.2 then
      (balancedCoolingHistoryAppend value.1.1 value.2.1 value.2.2, true)
    else
      (balancedCoolingHistoryAppend value.1.1 1 value.1.1.2.2.2, false)
  have hsome : Measurable someValue := by
    dsimp only [someValue]
    apply Measurable.ite
    · exact (measurable_snd.comp measurable_fst) (measurableSet_singleton true)
    · exact (measurable_balancedCoolingHistoryAppend (n := n)).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd) |>.prodMk
            measurable_const
    · exact ((happendConst 1).comp measurable_fst).prodMk measurable_const
  convert Measurable.optionElimParam
    (noneValue := noneValue) (someValue := someValue) hnone hsome using 1
  funext value
  rcases value with ⟨trace, result⟩
  cases result <;> rfl

/-- The ratio/state observation used by one trace phase.  Dead traces make no
further transition and emit failure deterministically. -/
noncomputable def scheduledBalancedTracePhaseObservationLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    ScheduledBalancedCoolingTrace q.n →
      Measure (Option (ℝ × AmbientSpace q.n)) := fun trace =>
  if trace.2 then
    if phase < terminalPhaseSteps q then
      scheduledBalancedCoolingRatioTransitionLaw parameters q I
        (scheduleValue q phase) (scheduleValue q (phase + 1))
        trace.1.2.2.2
    else
      scheduledBalancedCoolingUniformTransitionLaw parameters q I
        (terminalVariance q) trace.1.2.2.2
  else Measure.dirac none

theorem scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    Measurable
      (scheduledBalancedTracePhaseObservationLaw parameters q I phase) ∧
    ∀ trace, IsProbabilityMeasure
      (scheduledBalancedTracePhaseObservationLaw parameters q I phase trace) := by
  have hgaussian :=
    scheduledBalancedCoolingRatioTransitionLaw_measurable_and_probability
      parameters q I (scheduleValue_pos q phase) (scheduleValue q (phase + 1))
  have hterminal :=
    scheduledBalancedCoolingUniformTransitionLaw_measurable_and_probability
      parameters q I (terminalVariance_pos' q)
  constructor
  · unfold scheduledBalancedTracePhaseObservationLaw
    apply Measurable.ite
    · exact (measurable_snd : Measurable fun trace :
          ScheduledBalancedCoolingTrace q.n => trace.2)
        (measurableSet_singleton true)
    · split_ifs
      · exact hgaussian.1.comp (by fun_prop)
      · exact hterminal.1.comp (by fun_prop)
    · exact Measure.measurable_dirac.comp measurable_const
  · intro trace
    unfold scheduledBalancedTracePhaseObservationLaw
    split_ifs
    · exact hgaussian.2 _
    · exact hterminal.2 _
    · infer_instance

/-- Loss-preserving chronological phase kernel. -/
noncomputable def scheduledBalancedTracePhaseKernel
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    ScheduledBalancedCoolingTrace q.n →
      Measure (ScheduledBalancedCoolingTrace q.n) := fun trace =>
  (scheduledBalancedTracePhaseObservationLaw parameters q I phase trace).map
    (scheduledBalancedCoolingTraceAppend trace)

theorem scheduledBalancedTracePhaseKernel_measurable_and_probability
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ) :
    Measurable (scheduledBalancedTracePhaseKernel parameters q I phase) ∧
    ∀ trace, IsProbabilityMeasure
      (scheduledBalancedTracePhaseKernel parameters q I phase trace) := by
  have hobs :=
    scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
      parameters q I phase
  constructor
  · unfold scheduledBalancedTracePhaseKernel
    exact measurable_measure_map_param_variable hobs.1 hobs.2
      measurable_scheduledBalancedCoolingTraceAppend
  · intro trace
    unfold scheduledBalancedTracePhaseKernel
    let _ : IsProbabilityMeasure
        (scheduledBalancedTracePhaseObservationLaw parameters q I phase trace) :=
      hobs.2 trace
    exact Measure.isProbabilityMeasure_map
      ((measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
        (measurable_const.prodMk measurable_id)).aemeasurable

/-- One trace phase projects exactly to the existing executable history
kernel.  This is the key lumpability identity for changing state spaces. -/
theorem map_scheduledBalancedTracePhaseKernel_project
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    (scheduledBalancedTracePhaseKernel parameters q I phase trace).map
        scheduledBalancedCoolingTraceProject =
      scheduledBalancedForwardPhaseKernel parameters q I phase
        (scheduledBalancedCoolingTraceProject trace) := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false =>
      have happ : Measurable
          (scheduledBalancedCoolingTraceAppend (history, false)) :=
        (measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
          (measurable_const.prodMk measurable_id)
      change ((Measure.dirac none).map
          (scheduledBalancedCoolingTraceAppend (history, false))).map
            scheduledBalancedCoolingTraceProject = Measure.dirac none
      rw [Measure.map_map measurable_scheduledBalancedCoolingTraceProject happ,
        Measure.map_dirac'
          (measurable_scheduledBalancedCoolingTraceProject.comp happ)]
      rfl
  | true =>
      have happ : Measurable
          (scheduledBalancedCoolingTraceAppend (history, true)) :=
        (measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
          (measurable_const.prodMk measurable_id)
      unfold scheduledBalancedTracePhaseKernel
        scheduledBalancedTracePhaseObservationLaw
        scheduledBalancedForwardPhaseKernel
      simp only [scheduledBalancedCoolingTraceProject, if_true]
      split_ifs
      all_goals
        rw [Measure.map_map measurable_scheduledBalancedCoolingTraceProject
          happ]
        apply Measure.map_congr
        filter_upwards with result
        cases result <;> rfl

/-- Initial live trace. -/
def scheduledBalancedInitialTrace (point : AmbientSpace n) :
    ScheduledBalancedCoolingTrace n :=
  (((fun _ => 0), 0, 1, point), true)

theorem measurable_scheduledBalancedInitialTrace :
    Measurable (scheduledBalancedInitialTrace (n := n)) := by
  exact (measurable_const.prodMk <| measurable_const.prodMk <|
    measurable_const.prodMk measurable_id).prodMk measurable_const

@[simp] theorem scheduledBalancedInitialTrace_project
    (point : AmbientSpace n) :
    scheduledBalancedCoolingTraceProject (scheduledBalancedInitialTrace point) =
      balancedCoolingInitialHistory point := rfl

/-- Loss-preserving forward trace law. -/
noncomputable def scheduledBalancedForwardTraceLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phases : ℕ) :
    Measure (ScheduledBalancedCoolingTrace q.n) :=
  iteratedKernelLaw (scheduledBalancedTracePhaseKernel parameters q I)
    ((truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        scheduledBalancedInitialTrace) phases

/-- The loss-preserving trace is an exact refinement of the existing
scheduled chronological history law at every finite horizon. -/
theorem map_scheduledBalancedForwardTraceLaw_project
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : ∀ phases,
    (scheduledBalancedForwardTraceLaw parameters q I phases).map
        scheduledBalancedCoolingTraceProject =
      scheduledBalancedForwardHistoryLaw parameters q I phases := by
  intro phases
  induction phases with
  | zero =>
      unfold scheduledBalancedForwardTraceLaw
        scheduledBalancedForwardHistoryLaw iteratedKernelLaw
      rw [Measure.map_map measurable_scheduledBalancedCoolingTraceProject
        measurable_scheduledBalancedInitialTrace]
      apply Measure.map_congr
      filter_upwards with point
      rfl
  | succ phases ih =>
      let traceLaw :=
        scheduledBalancedForwardTraceLaw parameters q I phases
      let traceKernel :=
        scheduledBalancedTracePhaseKernel parameters q I phases
      let historyKernel :=
        scheduledBalancedForwardPhaseKernel parameters q I phases
      have htraceKernel :=
        scheduledBalancedTracePhaseKernel_measurable_and_probability
          parameters q I phases
      have hhistoryKernel :=
        scheduledBalancedForwardPhaseKernel_measurable_and_probability
          parameters q I phases
      change (traceLaw.bind traceKernel).map
          scheduledBalancedCoolingTraceProject =
        (scheduledBalancedForwardHistoryLaw parameters q I phases).bind
          historyKernel
      calc
        (traceLaw.bind traceKernel).map
            scheduledBalancedCoolingTraceProject =
          traceLaw.bind fun trace =>
            (traceKernel trace).map
              scheduledBalancedCoolingTraceProject :=
          map_bind_eq_bind_map_of_measurable traceLaw htraceKernel.1
            measurable_scheduledBalancedCoolingTraceProject
        _ = traceLaw.bind fun trace =>
            historyKernel (scheduledBalancedCoolingTraceProject trace) := by
          apply Measure.bind_congr_right
          filter_upwards with trace
          exact map_scheduledBalancedTracePhaseKernel_project
            parameters q I phases trace
        _ = (traceLaw.map scheduledBalancedCoolingTraceProject).bind
            historyKernel :=
          (map_bind_eq_bind_comp_state traceLaw
            measurable_scheduledBalancedCoolingTraceProject
            hhistoryKernel.1).symm
        _ = _ := by rw [ih]

/-! ## Structural trace invariants -/

/-- Chronological phase coordinate on the loss-preserving trace. -/
noncomputable def scheduledBalancedTraceChronologicalPhaseVariable
    (q : VolumeParams) (j : ℕ) : ScheduledBalancedCoolingTrace q.n → ℝ :=
  fun trace => balancedCoolingChronologicalPhaseVariable q j (some trace.1)

theorem measurable_scheduledBalancedTraceChronologicalPhaseVariable
    (q : VolumeParams) (j : ℕ) :
    Measurable (scheduledBalancedTraceChronologicalPhaseVariable q j) :=
  (measurable_balancedCoolingChronologicalPhaseVariable q j).comp
    (measurable_some.comp measurable_fst)

/-- A valid trace has the expected chronological length and stored product;
once dead, that product is zero. -/
def ScheduledBalancedCoolingTraceValid (m : ℕ)
    (trace : ScheduledBalancedCoolingTrace n) : Prop :=
  trace.1.2.1 = m ∧
    trace.1.2.2.1 = ∏ j ∈ Finset.range m, trace.1.1 j ∧
    (trace.2 = false → trace.1.2.2.1 = 0)

theorem measurableSet_scheduledBalancedCoolingTraceValid (m : ℕ) :
    MeasurableSet {trace : ScheduledBalancedCoolingTrace n |
      ScheduledBalancedCoolingTraceValid m trace} := by
  have hcount : Measurable fun trace : ScheduledBalancedCoolingTrace n =>
      trace.1.2.1 := by fun_prop
  have hproduct : Measurable fun trace : ScheduledBalancedCoolingTrace n =>
      trace.1.2.2.1 := by fun_prop
  have hsequence : Measurable fun trace : ScheduledBalancedCoolingTrace n =>
      ∏ j ∈ Finset.range m, trace.1.1 j := by fun_prop
  have hlive : MeasurableSet
      {trace : ScheduledBalancedCoolingTrace n | trace.2 = true} :=
    (measurable_snd : Measurable fun trace :
      ScheduledBalancedCoolingTrace n => trace.2) (measurableSet_singleton true)
  have hzero : MeasurableSet
      {trace : ScheduledBalancedCoolingTrace n | trace.1.2.2.1 = 0} :=
    measurableSet_eq_fun hproduct measurable_const
  rw [show {trace : ScheduledBalancedCoolingTrace n |
      ScheduledBalancedCoolingTraceValid m trace} =
      {trace | trace.1.2.1 = m} ∩
        ({trace | trace.1.2.2.1 = ∏ j ∈ Finset.range m, trace.1.1 j} ∩
          ({trace | trace.2 = true} ∪ {trace | trace.1.2.2.1 = 0})) by
    ext trace
    rcases trace with ⟨history, live⟩
    cases live <;> simp [ScheduledBalancedCoolingTraceValid, and_assoc]]
  exact (measurableSet_eq_fun hcount measurable_const).inter <|
    (measurableSet_eq_fun hproduct hsequence).inter (hlive.union hzero)

theorem ScheduledBalancedCoolingTraceValid.append
    {trace : ScheduledBalancedCoolingTrace n}
    (hvalid : ScheduledBalancedCoolingTraceValid m trace)
    (result : Option (ℝ × AmbientSpace n)) :
    ScheduledBalancedCoolingTraceValid (m + 1)
      (scheduledBalancedCoolingTraceAppend trace result) := by
  rcases trace with ⟨history, live⟩
  unfold ScheduledBalancedCoolingTraceValid at hvalid
  change history.2.1 = m ∧
    history.2.2.1 = ∏ j ∈ Finset.range m, history.1 j ∧
      (live = false → history.2.2.1 = 0) at hvalid
  have happend (ratio : ℝ) (point : AmbientSpace n) (nextLive : Bool)
      (hdead : nextLive = false → history.2.2.1 * ratio = 0) :
      ScheduledBalancedCoolingTraceValid (m + 1)
        (balancedCoolingHistoryAppend history ratio point, nextLive) := by
    unfold ScheduledBalancedCoolingTraceValid balancedCoolingHistoryAppend
    constructor
    · change history.2.1 + 1 = m + 1
      omega
    constructor
    · simp only
      rw [hvalid.1, prod_range_snoc_sequence, ← hvalid.2.1]
    · exact hdead
  cases live with
  | false =>
      cases result with
      | none =>
          simp only [scheduledBalancedCoolingTraceAppend, Bool.false_eq_true,
            if_false]
          exact happend 1 history.2.2.2 false fun _ => by
            simpa using hvalid.2.2 rfl
      | some result =>
          simp only [scheduledBalancedCoolingTraceAppend, Bool.false_eq_true,
            if_false]
          exact happend 1 history.2.2.2 false fun _ => by
            simpa using hvalid.2.2 rfl
  | true =>
      cases result with
      | none =>
          simp only [scheduledBalancedCoolingTraceAppend, if_true]
          exact happend 0 history.2.2.2 false fun _ => by simp
      | some result =>
          simp only [scheduledBalancedCoolingTraceAppend, if_true]
          exact happend result.1 result.2 true fun h => by simp at h

/-- Appending a later phase does not alter any earlier chronological
coordinate of a valid prefix. -/
theorem scheduledBalancedTraceChronologicalPhaseVariable_append_eq
    (q : VolumeParams) {m j : ℕ}
    {trace : ScheduledBalancedCoolingTrace q.n}
    (hvalid : ScheduledBalancedCoolingTraceValid m trace)
    (hmphase : m ≤ figureOneDependentPhaseCount q)
    (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (result : Option (ℝ × AmbientSpace q.n)) :
    scheduledBalancedTraceChronologicalPhaseVariable q j
        (scheduledBalancedCoolingTraceAppend trace result) =
      scheduledBalancedTraceChronologicalPhaseVariable q j trace := by
  rcases trace with ⟨history, live⟩
  unfold ScheduledBalancedCoolingTraceValid at hvalid
  change history.2.1 = m ∧
    history.2.2.1 = ∏ k ∈ Finset.range m, history.1 k ∧
      (live = false → history.2.2.1 = 0) at hvalid
  have hjrepr : j = (j - 1) + 1 := by omega
  have hne : j - 1 ≠ history.2.1 := by omega
  rw [hjrepr]
  unfold scheduledBalancedTraceChronologicalPhaseVariable
  rw [balancedCoolingChronologicalPhaseVariable_apply_succ q (j - 1)
    (by omega) (some (scheduledBalancedCoolingTraceAppend
      (history, live) result).1)]
  rw [balancedCoolingChronologicalPhaseVariable_apply_succ q (j - 1)
    (by omega) (some history)]
  cases live <;> cases result <;>
    simp only [scheduledBalancedCoolingTraceAppend,
      balancedCoolingHistoryAppend, Bool.false_eq_true, if_false, if_true]
  all_goals
    rw [if_neg hne]

/-- The trace's stored product agrees pointwise with the public executable
product after projection: dead traces have stored product zero. -/
theorem scheduledBalancedCoolingTrace_product_eq_project
    {trace : ScheduledBalancedCoolingTrace q.n}
    (hvalid : ScheduledBalancedCoolingTraceValid m trace) :
    trace.1.2.2.1 =
      balancedCoolingHistoryProduct q
        (scheduledBalancedCoolingTraceProject trace) := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false => simpa [scheduledBalancedCoolingTraceProject,
      balancedCoolingHistoryProduct] using hvalid.2.2 rfl
  | true => rfl

theorem scheduledBalancedTracePhaseKernel_ae_valid
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase m : ℕ)
    (trace : ScheduledBalancedCoolingTrace q.n)
    (hvalid : ScheduledBalancedCoolingTraceValid m trace) :
    ∀ᵐ next ∂scheduledBalancedTracePhaseKernel parameters q I phase trace,
      ScheduledBalancedCoolingTraceValid (m + 1) next := by
  unfold scheduledBalancedTracePhaseKernel
  apply (ae_map_iff
    ((measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
    (measurableSet_scheduledBalancedCoolingTraceValid _)).2
  filter_upwards with result
  exact hvalid.append result

theorem scheduledBalancedForwardTraceLaw_isProbabilityMeasure
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phases : ℕ) :
    IsProbabilityMeasure
      (scheduledBalancedForwardTraceLaw parameters q I phases) := by
  unfold scheduledBalancedForwardTraceLaw
  apply iteratedKernelLaw_isProbabilityMeasure
  · exact Measure.isProbabilityMeasure_map
      measurable_scheduledBalancedInitialTrace.aemeasurable
  · intro phase
    exact (scheduledBalancedTracePhaseKernel_measurable_and_probability
      parameters q I phase).1
  · intro phase trace
    exact (scheduledBalancedTracePhaseKernel_measurable_and_probability
      parameters q I phase).2 trace

/-- Every finite loss-preserving trace has exact chronological length and
product, and its stored product is zero after failure. -/
theorem scheduledBalancedForwardTraceLaw_ae_valid
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : ∀ phases,
    ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw parameters q I phases,
      ScheduledBalancedCoolingTraceValid phases trace := by
  intro phases
  induction phases with
  | zero =>
      unfold scheduledBalancedForwardTraceLaw iteratedKernelLaw
      apply (ae_map_iff measurable_scheduledBalancedInitialTrace.aemeasurable
        (measurableSet_scheduledBalancedCoolingTraceValid 0)).2
      filter_upwards with point
      simp [scheduledBalancedInitialTrace, ScheduledBalancedCoolingTraceValid]
  | succ phases ih =>
      let prefixLaw :=
        scheduledBalancedForwardTraceLaw parameters q I phases
      let kernel := scheduledBalancedTracePhaseKernel parameters q I phases
      let good : Set (ScheduledBalancedCoolingTrace q.n) :=
        {trace | ScheduledBalancedCoolingTraceValid (phases + 1) trace}
      have hgood : MeasurableSet good :=
        measurableSet_scheduledBalancedCoolingTraceValid _
      have hkernel : Measurable kernel :=
        (scheduledBalancedTracePhaseKernel_measurable_and_probability
          parameters q I phases).1
      change ∀ᵐ trace ∂prefixLaw.bind kernel,
        ScheduledBalancedCoolingTraceValid (phases + 1) trace
      apply MeasureTheory.mem_ae_iff.mpr
      change (prefixLaw.bind kernel) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl hkernel.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ih] with trace htrace
      exact MeasureTheory.mem_ae_iff.mp <|
        scheduledBalancedTracePhaseKernel_ae_valid
          parameters q I phases phases trace htrace

/-- On every valid completed trace, the stored product is exactly the product
of its chronological trace coordinates. -/
theorem dependentPhaseSampleProduct_scheduledBalancedTrace_eq
    (q : VolumeParams) (trace : ScheduledBalancedCoolingTrace q.n)
    (hvalid : ScheduledBalancedCoolingTraceValid
      (figureOneDependentPhaseCount q) trace) :
    dependentPhaseSampleProduct
        (scheduledBalancedTraceChronologicalPhaseVariable q)
        (figureOneDependentPhaseCount q) trace = trace.1.2.2.1 := by
  unfold dependentPhaseSampleProduct
  rw [hvalid.2.1]
  apply Finset.prod_congr rfl
  intro j hj
  unfold scheduledBalancedTraceChronologicalPhaseVariable
  rw [balancedCoolingChronologicalPhaseVariable_apply_succ q j
    (Finset.mem_range.mp hj) (some trace.1)]

/-- Finite chronological coordinate support for a loss-preserving trace. -/
def ScheduledBalancedCoolingTraceCoordinatesNonnegative (m : ℕ)
    (trace : ScheduledBalancedCoolingTrace n) : Prop :=
  BalancedCoolingHistoryHasNonnegativeCoordinates m (some trace.1)

theorem measurableSet_scheduledBalancedCoolingTraceCoordinatesNonnegative
    (m : ℕ) :
    MeasurableSet {trace : ScheduledBalancedCoolingTrace n |
      ScheduledBalancedCoolingTraceCoordinatesNonnegative m trace} := by
  exact (measurableSet_balancedCoolingHistoryHasNonnegativeCoordinates m).preimage
    (measurable_some.comp measurable_fst)

theorem scheduledBalancedTracePhaseObservationLaw_ae_total_nonnegative
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase : ℕ)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    ∀ᵐ result ∂scheduledBalancedTracePhaseObservationLaw
        parameters q I phase trace,
      ScheduledCollectedTotalNonnegative result := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false =>
      unfold scheduledBalancedTracePhaseObservationLaw
      apply (ae_dirac_iff measurableSet_scheduledCollectedTotalNonnegative).2
      trivial
  | true =>
      unfold scheduledBalancedTracePhaseObservationLaw
      simp only [if_true]
      split_ifs
      · exact scheduledBalancedCoolingRatioTransitionLaw_ae_ratio_nonnegative
          parameters q I (scheduleValue_pos q phase)
            (scheduleValue q (phase + 1)) history.2.2.2
      · exact scheduledBalancedCoolingUniformTransitionLaw_ae_ratio_nonnegative
          parameters q I (terminalVariance_pos' q) history.2.2.2

theorem ScheduledBalancedCoolingTraceCoordinatesNonnegative.append
    {trace : ScheduledBalancedCoolingTrace n}
    (hcoordinates : ScheduledBalancedCoolingTraceCoordinatesNonnegative m trace)
    {result : Option (ℝ × AmbientSpace n)}
    (hresult : ScheduledCollectedTotalNonnegative result) :
    ScheduledBalancedCoolingTraceCoordinatesNonnegative (m + 1)
      (scheduledBalancedCoolingTraceAppend trace result) := by
  rcases trace with ⟨history, live⟩
  cases live with
  | false =>
      cases result <;>
        simp only [ScheduledBalancedCoolingTraceCoordinatesNonnegative,
          scheduledBalancedCoolingTraceAppend, Bool.false_eq_true, if_false]
      all_goals
        have hone : ScheduledCollectedTotalNonnegative
            (some ((1 : ℝ), history.2.2.2)) := by
          norm_num [ScheduledCollectedTotalNonnegative]
        have h := hcoordinates.snocTerminal hone
        rw [balancedCoolingHistorySnocTerminal_some] at h
        exact h
  | true =>
      cases result with
      | none =>
          simp only [ScheduledBalancedCoolingTraceCoordinatesNonnegative,
            scheduledBalancedCoolingTraceAppend, if_true]
          have hzero : ScheduledCollectedTotalNonnegative
              (some ((0 : ℝ), history.2.2.2)) := by
            norm_num [ScheduledCollectedTotalNonnegative]
          have h := hcoordinates.snocTerminal hzero
          rw [balancedCoolingHistorySnocTerminal_some] at h
          exact h
      | some result =>
          simp only [ScheduledBalancedCoolingTraceCoordinatesNonnegative,
            scheduledBalancedCoolingTraceAppend, if_true]
          have h := hcoordinates.snocTerminal hresult
          rw [balancedCoolingHistorySnocTerminal_some] at h
          exact h

theorem scheduledBalancedTracePhaseKernel_ae_coordinatesNonnegative
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (phase m : ℕ)
    (trace : ScheduledBalancedCoolingTrace q.n)
    (hcoordinates : ScheduledBalancedCoolingTraceCoordinatesNonnegative m trace) :
    ∀ᵐ next ∂scheduledBalancedTracePhaseKernel parameters q I phase trace,
      ScheduledBalancedCoolingTraceCoordinatesNonnegative (m + 1) next := by
  unfold scheduledBalancedTracePhaseKernel
  apply (ae_map_iff
    ((measurable_scheduledBalancedCoolingTraceAppend (n := q.n)).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
    (measurableSet_scheduledBalancedCoolingTraceCoordinatesNonnegative _)).2
  filter_upwards [
    scheduledBalancedTracePhaseObservationLaw_ae_total_nonnegative
      parameters q I phase trace] with result hresult
  exact hcoordinates.append hresult

theorem scheduledBalancedForwardTraceLaw_ae_coordinatesNonnegative
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) : ∀ phases,
    ∀ᵐ trace ∂scheduledBalancedForwardTraceLaw parameters q I phases,
      ScheduledBalancedCoolingTraceCoordinatesNonnegative phases trace := by
  intro phases
  induction phases with
  | zero =>
      unfold scheduledBalancedForwardTraceLaw iteratedKernelLaw
      apply (ae_map_iff measurable_scheduledBalancedInitialTrace.aemeasurable
        (measurableSet_scheduledBalancedCoolingTraceCoordinatesNonnegative 0)).2
      filter_upwards with point
      simp [ScheduledBalancedCoolingTraceCoordinatesNonnegative,
        ScheduledBalancedCoolingTraceValid, scheduledBalancedInitialTrace,
        BalancedCoolingHistoryHasNonnegativeCoordinates]
  | succ phases ih =>
      let prefixLaw :=
        scheduledBalancedForwardTraceLaw parameters q I phases
      let kernel := scheduledBalancedTracePhaseKernel parameters q I phases
      let good : Set (ScheduledBalancedCoolingTrace q.n) :=
        {trace |
          ScheduledBalancedCoolingTraceCoordinatesNonnegative
            (phases + 1) trace}
      have hgood : MeasurableSet good :=
        measurableSet_scheduledBalancedCoolingTraceCoordinatesNonnegative _
      have hkernel : Measurable kernel :=
        (scheduledBalancedTracePhaseKernel_measurable_and_probability
          parameters q I phases).1
      change ∀ᵐ trace ∂prefixLaw.bind kernel,
        ScheduledBalancedCoolingTraceCoordinatesNonnegative
          (phases + 1) trace
      apply MeasureTheory.mem_ae_iff.mpr
      change (prefixLaw.bind kernel) goodᶜ = 0
      rw [Measure.bind_apply hgood.compl hkernel.aemeasurable]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ih] with trace htrace
      exact MeasureTheory.mem_ae_iff.mp <|
        scheduledBalancedTracePhaseKernel_ae_coordinatesNonnegative
          parameters q I phases phases trace htrace

#print axioms map_scheduledBalancedTracePhaseKernel_project
#print axioms map_scheduledBalancedForwardTraceLaw_project
#print axioms scheduledBalancedTraceChronologicalPhaseVariable_append_eq
#print axioms scheduledBalancedForwardTraceLaw_ae_valid
#print axioms scheduledBalancedForwardTraceLaw_ae_coordinatesNonnegative

end ArlibCommunity.Algorithms.CV18
