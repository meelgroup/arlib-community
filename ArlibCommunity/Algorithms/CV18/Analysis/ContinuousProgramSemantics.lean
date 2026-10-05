/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Pseudocode
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.MeasurableLIntegral

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-- The exact measurability obligations under which the Giry interpreter is a
probability law rather than Mathlib's zero fallback for a nonmeasurable bind. -/
def MembershipOracleProgram.ExecutionMeasurable
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool) :
    MembershipOracleProgram n Result → Prop
  | .pure _ => True
  | .query point next => ExecutionMeasurable oracle (next (oracle point))
  | .randomNat law next =>
      AEMeasurable (fun seed => run oracle (next seed)) law.toMeasure ∧
        ∀ᵐ seed ∂law.toMeasure, ExecutionMeasurable oracle (next seed)
  | .randomPoint law _ next =>
      AEMeasurable (fun point => run oracle (next point)) law ∧
        ∀ᵐ point ∂law, ExecutionMeasurable oracle (next point)
  | .randomReal law _ next =>
      AEMeasurable (fun value => run oracle (next value)) law ∧
        ∀ᵐ value ∂law, ExecutionMeasurable oracle (next value)

theorem MembershipOracleProgram.run_isProbabilityMeasure
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result)
    (hmeas : program.ExecutionMeasurable oracle) :
    IsProbabilityMeasure (program.run oracle) := by
  induction program with
  | pure result =>
      rw [MembershipOracleProgram.run]
      infer_instance
  | query point next ih =>
      simp only [MembershipOracleProgram.run]
      change ExecutionMeasurable oracle (next (oracle point)) at hmeas
      have hprob := ih (oracle point) hmeas
      let _ : IsProbabilityMeasure (run oracle (next (oracle point))) := hprob
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  | randomNat law next ih =>
      simp only [ExecutionMeasurable] at hmeas
      simp only [MembershipOracleProgram.run]
      apply MeasureTheory.isProbabilityMeasure_bind hmeas.1
      filter_upwards [hmeas.2] with seed hseed
      exact ih seed hseed
  | randomPoint law lawProbability next ih =>
      simp only [ExecutionMeasurable] at hmeas
      simp only [MembershipOracleProgram.run]
      let _ : IsProbabilityMeasure law := lawProbability
      apply MeasureTheory.isProbabilityMeasure_bind hmeas.1
      filter_upwards [hmeas.2] with point hpoint
      exact ih point hpoint
  | randomReal law lawProbability next ih =>
      simp only [ExecutionMeasurable] at hmeas
      simp only [MembershipOracleProgram.run]
      let _ : IsProbabilityMeasure law := lawProbability
      apply MeasureTheory.isProbabilityMeasure_bind hmeas.1
      filter_upwards [hmeas.2] with value hvalue
      exact ih value hvalue

/-- Lebesgue measure on the centered proposal ball, with its finiteness proof. -/
noncomputable def centeredClosedBallFiniteMeasure (n : ℕ) (radius : ℝ) :
    FiniteMeasure (AmbientSpace n) :=
  ⟨volume.restrict (Metric.closedBall 0 radius), ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_closedBall_lt_top⟩⟩

/-- Normalized Lebesgue measure on the proposal ball centered at zero. -/
noncomputable def centeredClosedBallMeasure (n : ℕ) (radius : ℝ) :
    Measure (AmbientSpace n) :=
  (centeredClosedBallFiniteMeasure n radius).normalize

instance centeredClosedBallMeasure_isProbabilityMeasure (n : ℕ) (radius : ℝ) :
    IsProbabilityMeasure (centeredClosedBallMeasure n radius) := by
  unfold centeredClosedBallMeasure
  infer_instance

/-- Uniform proposal measure on a ball, written as a translated centered law.
This presentation makes dependence on the current point measurably explicit. -/
noncomputable def uniformClosedBallMeasure (n : ℕ) (center : AmbientSpace n)
    (radius : ℝ) : Measure (AmbientSpace n) :=
  (centeredClosedBallMeasure n radius).map fun offset => center + offset

instance uniformClosedBallMeasure_isProbabilityMeasure
    (n : ℕ) (center : AmbientSpace n) (radius : ℝ) :
    IsProbabilityMeasure (uniformClosedBallMeasure n center radius) := by
  unfold uniformClosedBallMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Lebesgue measure on `[0,1]`, packaged with its finiteness proof. -/
noncomputable def uniformUnitIntervalFiniteMeasure : FiniteMeasure ℝ :=
  ⟨volume.restrict (Set.Icc 0 1), ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_Icc_lt_top⟩⟩

/-- Normalized Lebesgue measure on `[0,1]`, used for Metropolis and laziness
coins without discretizing their acceptance thresholds. -/
noncomputable def uniformUnitIntervalMeasure : Measure ℝ :=
  uniformUnitIntervalFiniteMeasure.normalize

instance uniformUnitIntervalMeasure_isProbabilityMeasure :
    IsProbabilityMeasure uniformUnitIntervalMeasure := by
  unfold uniformUnitIntervalMeasure
  infer_instance

/-- All executions of a program traverse exactly `count` query nodes. This is
syntax-level accounting and is independent of any probability semantics. -/
inductive MembershipOracleProgram.FixedQueryCount
    {n : ℕ} {Result : Type} :
    MembershipOracleProgram n Result → ℕ → Prop where
  | pure (result : Result) : FixedQueryCount (.pure result) 0
  | query (point : AmbientSpace n)
      (next : Bool → MembershipOracleProgram n Result) (count : ℕ)
      (hnext : ∀ answer, FixedQueryCount (next answer) count) :
      FixedQueryCount (.query point next) (count + 1)
  | randomNat (law : PMF ℕ)
      (next : ℕ → MembershipOracleProgram n Result) (count : ℕ)
      (hnext : ∀ seed, FixedQueryCount (next seed) count) :
      FixedQueryCount (.randomNat law next) count
  | randomPoint (law : Measure (AmbientSpace n)) (hprob : IsProbabilityMeasure law)
      (next : AmbientSpace n → MembershipOracleProgram n Result) (count : ℕ)
      (hnext : ∀ point, FixedQueryCount (next point) count) :
      FixedQueryCount (.randomPoint law hprob next) count
  | randomReal (law : Measure ℝ) (hprob : IsProbabilityMeasure law)
      (next : ℝ → MembershipOracleProgram n Result) (count : ℕ)
      (hnext : ∀ value, FixedQueryCount (next value) count) :
      FixedQueryCount (.randomReal law hprob next) count

theorem MembershipOracleProgram.FixedQueryCount.bind
    {n : ℕ} {A B : Type}
    {program : MembershipOracleProgram n A} {next : A → MembershipOracleProgram n B}
    {first second : ℕ} (hprogram : program.FixedQueryCount first)
    (hnext : ∀ result, (next result).FixedQueryCount second) :
    (program.bind next).FixedQueryCount (first + second) := by
  induction hprogram with
  | pure result =>
      simpa [MembershipOracleProgram.bind] using hnext result
  | query point branch count hbranch ih =>
      simp only [MembershipOracleProgram.bind]
      rw [Nat.add_assoc, Nat.add_comm 1 second, ← Nat.add_assoc]
      exact .query point _ _ fun answer => ih answer
  | randomNat law branch count hbranch ih =>
      exact .randomNat law _ _ fun seed => ih seed
  | randomPoint law hprob branch count hbranch ih =>
      exact .randomPoint law hprob _ _ fun point => ih point
  | randomReal law hprob branch count hbranch ih =>
      exact .randomReal law hprob _ _ fun value => ih value

theorem MembershipOracleProgram.FixedQueryCount.run_count_eq_one
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    {program : MembershipOracleProgram n Result} {count : ℕ}
    (hcount : program.FixedQueryCount count)
    (oracle : AmbientSpace n → Bool)
    (hmeas : program.ExecutionMeasurable oracle) :
    program.run oracle {outcome | outcome.2 = count} = 1 := by
  induction hcount with
  | pure result =>
      simp [MembershipOracleProgram.run]
  | query point next count hnext ih =>
      change ExecutionMeasurable oracle (next (oracle point)) at hmeas
      rw [MembershipOracleProgram.run, Measure.map_apply (by fun_prop) (by measurability)]
      simpa only [Set.preimage_ofPred_eq, Prod.snd, Nat.add_right_cancel_iff] using
        ih (oracle point) hmeas
  | randomNat law next count hnext ih =>
      simp only [ExecutionMeasurable] at hmeas
      rw [MembershipOracleProgram.run,
        Measure.bind_apply (by measurability) hmeas.1]
      have heq :
          (fun seed => run oracle (next seed) {outcome | outcome.2 = count}) =ᵐ[law.toMeasure]
            fun _ => 1 := by
        filter_upwards [hmeas.2] with seed hseed
        exact ih seed hseed
      rw [lintegral_congr_ae heq]
      simp
  | randomPoint law hprob next count hnext ih =>
      simp only [ExecutionMeasurable] at hmeas
      rw [MembershipOracleProgram.run,
        Measure.bind_apply (by measurability) hmeas.1]
      have heq :
          (fun point => run oracle (next point) {outcome | outcome.2 = count}) =ᵐ[law]
            fun _ => 1 := by
        filter_upwards [hmeas.2] with point hpoint
        exact ih point hpoint
      rw [lintegral_congr_ae heq]
      let _ : IsProbabilityMeasure law := hprob
      simp
  | randomReal law hprob next count hnext ih =>
      simp only [ExecutionMeasurable] at hmeas
      rw [MembershipOracleProgram.run,
        Measure.bind_apply (by measurability) hmeas.1]
      have heq :
          (fun value => run oracle (next value) {outcome | outcome.2 = count}) =ᵐ[law]
            fun _ => 1 := by
        filter_upwards [hmeas.2] with value hvalue
        exact ih value hvalue
      rw [lintegral_congr_ae heq]
      let _ : IsProbabilityMeasure law := hprob
      simp

/-- Metropolis acceptance probability for two points at variance `sigma2`. -/
noncomputable def gaussianMetropolisAcceptance {n : ℕ} (sigma2 : ℝ)
    (x y : AmbientSpace n) : ℝ :=
  min 1 (Real.exp (-‖y‖ ^ 2 / (2 * sigma2)) /
    Real.exp (-‖x‖ ^ 2 / (2 * sigma2)))

/-- One implementable Metropolis ball-walk step. It proposes from the full
ball, asks the oracle whether the proposal is in the body, and uses a genuine
uniform real coin for the Metropolis filter. -/
noncomputable def continuousMetropolisProposalProgram {n : ℕ}
    (sigma2 : ℝ) (current proposal : AmbientSpace n) :
    MembershipOracleProgram n (AmbientSpace n) :=
  .query proposal fun inside =>
    if inside then
      .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
        .pure <| if coin ≤ gaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current
    else .pure current

noncomputable def continuousMetropolisBallStep {n : ℕ}
    (sigma2 delta : ℝ) (current : AmbientSpace n) :
    MembershipOracleProgram n (AmbientSpace n) :=
  .randomPoint (uniformClosedBallMeasure n current delta) inferInstance fun proposal =>
    continuousMetropolisProposalProgram sigma2 current proposal

theorem continuousMetropolisBallStep_fixedQueryCount {n : ℕ}
    (sigma2 delta : ℝ) (current : AmbientSpace n) :
    (continuousMetropolisBallStep sigma2 delta current).FixedQueryCount 1 := by
  apply MembershipOracleProgram.FixedQueryCount.randomPoint
  intro proposal
  unfold continuousMetropolisProposalProgram
  apply MembershipOracleProgram.FixedQueryCount.query
  intro inside
  cases inside <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact MembershipOracleProgram.FixedQueryCount.pure _
  · apply MembershipOracleProgram.FixedQueryCount.randomReal
    intro coin
    exact MembershipOracleProgram.FixedQueryCount.pure _

/-- A fixed-length continuous Metropolis ball walk, threading the accepted
endpoint into the next proposal exactly as required for warm starts. -/
noncomputable def continuousMetropolisBallWalk {n : ℕ}
    (sigma2 delta : ℝ) : ℕ → AmbientSpace n →
      MembershipOracleProgram n (AmbientSpace n)
  | 0, current => .pure current
  | steps + 1, current =>
      (continuousMetropolisBallStep sigma2 delta current).bind
        (continuousMetropolisBallWalk sigma2 delta steps)

theorem continuousMetropolisBallWalk_fixedQueryCount {n : ℕ}
    (sigma2 delta : ℝ) : ∀ (steps : ℕ) (current : AmbientSpace n),
    (continuousMetropolisBallWalk sigma2 delta steps current).FixedQueryCount steps := by
  intro steps
  induction steps with
  | zero =>
      intro current
      exact .pure current
  | succ steps ih =>
      intro current
      simp only [continuousMetropolisBallWalk]
      have hbind := (continuousMetropolisBallStep_fixedQueryCount sigma2 delta current).bind
        (fun point => ih point)
      simpa [Nat.add_comm] using hbind

theorem MembershipOracle.measurable_query {n : ℕ} {I : VolumeInput n}
    (oracle : MembershipOracle I) : Measurable oracle.query := by
  apply measurable_to_bool
  have hpreimage : oracle.query ⁻¹' {true} = (I.body : Set (AmbientSpace n)) := by
    ext x
    simpa using oracle.correct x
  rw [hpreimage]
  exact I.body.isClosed.measurableSet

theorem measurable_measure_map_param
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) [SFinite μ] {f : α → β → γ}
    (hf : Measurable fun p : α × β => f p.1 p.2) :
    Measurable fun a => μ.map (f a) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hfa : ∀ a, Measurable (f a) := fun a =>
    hf.comp (measurable_const.prodMk measurable_id)
  simp_rw [Measure.map_apply (hfa _) hs]
  have hindicator : Measurable fun p : α × β =>
      s.indicator (fun _ => (1 : ENNReal)) (f p.1 p.2) :=
    measurable_const.indicator (hf hs)
  have hmeasure (a : α) :
      (∫⁻ b, s.indicator (fun _ => (1 : ENNReal)) (f a b) ∂μ) =
        μ (f a ⁻¹' s) := by
    have heq : (fun b => s.indicator (fun _ => (1 : ENNReal)) (f a b)) =
        (f a ⁻¹' s).indicator (fun _ => (1 : ENNReal)) := by
      funext b
      simp only [Set.indicator, Set.mem_preimage]
      split_ifs <;> simp_all
    rw [heq]
    exact MeasureTheory.lintegral_indicator_one (hfa a hs)
  have hm := hindicator.lintegral_prod_right' (ν := μ)
  simpa only [hmeasure] using hm

theorem measurable_measure_bind_param
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) [SFinite μ] {f : α → β → Measure γ}
    (hf : Measurable fun p : α × β => f p.1 p.2) :
    Measurable fun a => μ.bind (f a) := by
  unfold Measure.bind
  exact Measure.measurable_join.comp (measurable_measure_map_param μ hf)

/-- Jointly measurable pushforward when both the source measure and the map
depend on a parameter.  Probability of the source supplies the s-finiteness
needed by the kernel section lemma. -/
theorem measurable_measure_map_param_variable
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : α → Measure β} (hμ : Measurable μ)
    (hprob : ∀ a, IsProbabilityMeasure (μ a))
    {f : α → β → γ} (hf : Measurable fun p : α × β => f p.1 p.2) :
    Measurable fun a => (μ a).map (f a) := by
  let κ : ProbabilityTheory.Kernel α β := ⟨μ, hμ⟩
  let _ : ProbabilityTheory.IsMarkovKernel κ :=
    ⟨fun a => hprob a⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hfa : ∀ a, Measurable (f a) := fun a =>
    hf.comp (measurable_const.prodMk measurable_id)
  simp_rw [Measure.map_apply (hfa _) hs]
  change Measurable fun a =>
    κ a (Prod.mk a ⁻¹' {p : α × β | f p.1 p.2 ∈ s})
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
    (κ := κ) (hf hs)

/-- Jointly measurable Giry bind with a parameter-dependent source and
parameter-dependent continuation. -/
theorem measurable_measure_bind_param_variable
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : α → Measure β} (hμ : Measurable μ)
    (hprob : ∀ a, IsProbabilityMeasure (μ a))
    {f : α → β → Measure γ}
    (hf : Measurable fun p : α × β => f p.1 p.2) :
    Measurable fun a => (μ a).bind (f a) := by
  unfold Measure.bind
  exact Measure.measurable_join.comp
    (measurable_measure_map_param_variable hμ hprob hf)

theorem measurable_uniformClosedBallMeasure (n : ℕ) (radius : ℝ) :
    Measurable fun center : AmbientSpace n =>
      uniformClosedBallMeasure n center radius := by
  unfold uniformClosedBallMeasure
  apply measurable_measure_map_param
  fun_prop

/-- The one-query outcome law after a proposal has been selected. -/
noncomputable def continuousMetropolisProposalLaw {n : ℕ}
    (oracle : AmbientSpace n → Bool) (sigma2 : ℝ)
    (current proposal : AmbientSpace n) : Measure (AmbientSpace n × ℕ) :=
  if oracle proposal then
    uniformUnitIntervalMeasure.map fun coin =>
      ((if coin ≤ gaussianMetropolisAcceptance sigma2 current proposal
          then proposal else current), 1)
  else Measure.dirac (current, 1)

theorem measurable_continuousMetropolisProposalLaw {n : ℕ}
    (I : VolumeInput n) (oracle : MembershipOracle I) (sigma2 : ℝ) :
    Measurable fun p : AmbientSpace n × AmbientSpace n =>
      continuousMetropolisProposalLaw oracle.query sigma2 p.1 p.2 := by
  have haccept : Measurable fun p : AmbientSpace n × AmbientSpace n =>
      gaussianMetropolisAcceptance sigma2 p.1 p.2 := by
    unfold gaussianMetropolisAcceptance
    fun_prop
  have hout : Measurable fun p :
      (AmbientSpace n × AmbientSpace n) × ℝ =>
      ((if p.2 ≤ gaussianMetropolisAcceptance sigma2 p.1.1 p.1.2
          then p.1.2 else p.1.1), 1) := by
    have hpoint : Measurable fun p :
        (AmbientSpace n × AmbientSpace n) × ℝ =>
        if p.2 ≤ gaussianMetropolisAcceptance sigma2 p.1.1 p.1.2
          then p.1.2 else p.1.1 := Measurable.ite
      (measurableSet_le measurable_snd (haccept.comp measurable_fst))
      (measurable_snd.comp measurable_fst)
      (measurable_fst.comp measurable_fst)
    exact hpoint.prodMk measurable_const
  unfold continuousMetropolisProposalLaw
  apply Measurable.ite
  · change MeasurableSet ((oracle.query ∘ Prod.snd) ⁻¹' {true})
    exact (oracle.measurable_query.comp measurable_snd) (measurableSet_singleton true)
  · exact measurable_measure_map_param uniformUnitIntervalMeasure hout
  · exact Measure.measurable_dirac.comp (measurable_fst.prodMk measurable_const)

theorem continuousMetropolisProposalLaw_isProbabilityMeasure {n : ℕ}
    (oracle : AmbientSpace n → Bool) (sigma2 : ℝ)
    (current proposal : AmbientSpace n) :
    IsProbabilityMeasure
      (continuousMetropolisProposalLaw oracle sigma2 current proposal) := by
  unfold continuousMetropolisProposalLaw
  split
  · have hcoin : Measurable fun coin : ℝ =>
        ((if coin ≤ gaussianMetropolisAcceptance sigma2 current proposal
            then proposal else current), 1) :=
      (Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const).prodMk measurable_const
    exact Measure.isProbabilityMeasure_map hcoin.aemeasurable
  · infer_instance

theorem run_continuousMetropolisProposalProgram {n : ℕ}
    (oracle : AmbientSpace n → Bool) (sigma2 : ℝ)
    (current proposal : AmbientSpace n) :
    (continuousMetropolisProposalProgram sigma2 current proposal).run oracle =
      continuousMetropolisProposalLaw oracle sigma2 current proposal := by
  unfold continuousMetropolisProposalProgram continuousMetropolisProposalLaw
  simp only [MembershipOracleProgram.run, apply_ite]
  split
  · have hcoin : Measurable fun coin : ℝ =>
        ((if coin ≤ gaussianMetropolisAcceptance sigma2 current proposal
            then proposal else current), 0) :=
      (Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const).prodMk measurable_const
    rw [show (fun value : ℝ =>
        if value ≤ gaussianMetropolisAcceptance sigma2 current proposal
          then Measure.dirac (proposal, 0) else Measure.dirac (current, 0)) =
        (fun value => Measure.dirac
          ((if value ≤ gaussianMetropolisAcceptance sigma2 current proposal
              then proposal else current), 0)) by
      funext value
      split_ifs <;> rfl]
    rw [Measure.bind_dirac_eq_map uniformUnitIntervalMeasure hcoin]
    rw [Measure.map_map (by fun_prop) hcoin]
    congr 1
  · rw [Measure.map_dirac]

/-- The explicit Markov kernel of one Metropolis ball step. Writing proposals
as centered offsets avoids a parameter-dependent source measure. -/
noncomputable def continuousMetropolisBallStepLaw {n : ℕ}
    (oracle : AmbientSpace n → Bool) (sigma2 delta : ℝ)
    (current : AmbientSpace n) : Measure (AmbientSpace n × ℕ) :=
  (centeredClosedBallMeasure n delta).bind fun offset =>
    continuousMetropolisProposalLaw oracle sigma2 current (current + offset)

theorem measurable_continuousMetropolisBallStepLaw {n : ℕ}
    (I : VolumeInput n) (oracle : MembershipOracle I) (sigma2 delta : ℝ) :
    Measurable fun current : AmbientSpace n =>
      continuousMetropolisBallStepLaw oracle.query sigma2 delta current := by
  unfold continuousMetropolisBallStepLaw
  apply measurable_measure_bind_param
  exact (measurable_continuousMetropolisProposalLaw I oracle sigma2).comp
    (measurable_fst.prodMk (measurable_fst.add measurable_snd))

theorem continuousMetropolisBallStepLaw_isProbabilityMeasure {n : ℕ}
    (I : VolumeInput n) (oracle : MembershipOracle I) (sigma2 delta : ℝ)
    (current : AmbientSpace n) :
    IsProbabilityMeasure
      (continuousMetropolisBallStepLaw oracle.query sigma2 delta current) := by
  unfold continuousMetropolisBallStepLaw
  apply MeasureTheory.isProbabilityMeasure_bind
    ((measurable_continuousMetropolisProposalLaw I oracle sigma2).comp
      (measurable_const.prodMk (measurable_const.add measurable_id))).aemeasurable
  filter_upwards with offset
  exact continuousMetropolisProposalLaw_isProbabilityMeasure
    oracle.query sigma2 current (current + offset)

theorem run_continuousMetropolisBallStep {n : ℕ}
    (I : VolumeInput n) (oracle : MembershipOracle I)
    (sigma2 delta : ℝ) (current : AmbientSpace n) :
    (continuousMetropolisBallStep sigma2 delta current).run oracle.query =
      continuousMetropolisBallStepLaw oracle.query sigma2 delta current := by
  simp only [continuousMetropolisBallStep,
    MembershipOracleProgram.run]
  rw [show (fun proposal =>
      (continuousMetropolisProposalProgram sigma2 current proposal).run oracle.query) =
      (fun proposal =>
        continuousMetropolisProposalLaw oracle.query sigma2 current proposal) by
    funext proposal
    exact run_continuousMetropolisProposalProgram
      oracle.query sigma2 current proposal]
  ext s hs
  have hproposal : Measurable fun proposal : AmbientSpace n =>
      continuousMetropolisProposalLaw oracle.query sigma2 current proposal :=
    (measurable_continuousMetropolisProposalLaw I oracle sigma2).comp
      (measurable_const.prodMk measurable_id)
  have hoffset : Measurable fun offset : AmbientSpace n =>
      continuousMetropolisProposalLaw oracle.query sigma2 current (current + offset) :=
    hproposal.comp (measurable_const.add measurable_id)
  unfold continuousMetropolisBallStepLaw uniformClosedBallMeasure
  rw [Measure.bind_apply hs hproposal.aemeasurable,
    Measure.bind_apply hs hoffset.aemeasurable]
  exact lintegral_map (Measure.measurable_coe hs |>.comp hproposal)
    (by fun_prop)

theorem continuousMetropolisBallStep_executionMeasurable
    {n : ℕ} (I : VolumeInput n) (oracle : MembershipOracle I)
    (sigma2 delta : ℝ) (current : AmbientSpace n) :
    (continuousMetropolisBallStep sigma2 delta current).ExecutionMeasurable oracle.query := by
  simp only [continuousMetropolisBallStep,
    MembershipOracleProgram.ExecutionMeasurable]
  constructor
  · apply Measurable.aemeasurable
    simp only [continuousMetropolisProposalProgram,
      MembershipOracleProgram.run, apply_ite]
    apply Measurable.ite
    · change MeasurableSet (oracle.query ⁻¹' {true})
      exact oracle.measurable_query (measurableSet_singleton true)
    · have haccept : Measurable fun point : AmbientSpace n =>
          gaussianMetropolisAcceptance sigma2 current point := by
        unfold gaussianMetropolisAcceptance
        fun_prop
      have hout : Measurable fun p : AmbientSpace n × ℝ =>
          ((if p.2 ≤ gaussianMetropolisAcceptance sigma2 current p.1
              then p.1 else current), 1) := by
        exact (Measurable.ite
          (measurableSet_le measurable_snd (haccept.comp measurable_fst))
          measurable_fst measurable_const).prodMk measurable_const
      have hmap : Measurable fun point : AmbientSpace n =>
          uniformUnitIntervalMeasure.map fun coin =>
            ((if coin ≤ gaussianMetropolisAcceptance sigma2 current point
                then point else current), 1) :=
        measurable_measure_map_param uniformUnitIntervalMeasure hout
      convert hmap using 1
      funext point
      have hcoin : Measurable fun coin : ℝ =>
          ((if coin ≤ gaussianMetropolisAcceptance sigma2 current point
              then point else current), 0) :=
        (Measurable.ite (measurableSet_le measurable_id measurable_const)
          measurable_const measurable_const).prodMk measurable_const
      rw [show (fun value : ℝ =>
          if value ≤ gaussianMetropolisAcceptance sigma2 current point
            then Measure.dirac (point, 0) else Measure.dirac (current, 0)) =
          (fun value => Measure.dirac
            ((if value ≤ gaussianMetropolisAcceptance sigma2 current point
                then point else current), 0)) by
        funext value
        split_ifs <;> rfl]
      rw [Measure.bind_dirac_eq_map uniformUnitIntervalMeasure hcoin]
      rw [Measure.map_map (by fun_prop) hcoin]
      congr 1
    · fun_prop
  · filter_upwards with proposal
    change MembershipOracleProgram.ExecutionMeasurable oracle.query
      (.query proposal fun inside =>
        if inside then
          .randomReal uniformUnitIntervalMeasure inferInstance fun coin =>
            .pure <| if coin ≤ gaussianMetropolisAcceptance sigma2 current proposal
              then proposal else current
        else .pure current)
    simp only [MembershipOracleProgram.ExecutionMeasurable]
    split
    · constructor
      · apply Measurable.aemeasurable
        simp only [MembershipOracleProgram.run]
        apply Measure.measurable_dirac.comp
        exact (Measurable.ite
          (measurableSet_le measurable_id measurable_const)
          measurable_const measurable_const).prodMk measurable_const
      · filter_upwards with coin
        trivial
    · trivial

/-- Continuous counterparts of the three Figure-1 primitives. Their programs
remain uniform in the input body and can observe it only through query nodes. -/
structure ContinuousVolumeCoolingPrimitives where
  initialSample :
    (q : VolumeParams) →
      MembershipOracleProgram q.n (Option (AmbientSpace q.n))
  ratioEstimate :
    (q : VolumeParams) → (sigma2 tau2 : ℝ) → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  uniformRatioEstimate :
    (q : VolumeParams) → (sigma2 : ℝ) → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option ℝ)

noncomputable def continuousCoolingProduct (P : ContinuousVolumeCoolingPrimitives)
    (q : VolumeParams) :
    List ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | [], point => .pure (some (1, point))
  | [_], point => .pure (some (1, point))
  | sigma2 :: tau2 :: rest, point =>
      (P.ratioEstimate q sigma2 tau2 point).bind fun phase =>
        match phase with
        | none => .pure none
        | some (ratio, nextPoint) =>
            (continuousCoolingProduct P q (tau2 :: rest) nextPoint).bind fun tail =>
              .pure <| match tail with
                | some (product, lastPoint) => some (ratio * product, lastPoint)
                | none => none
termination_by variances => variances.length

/-- Figure 1 with non-atomic proposal support. Aborts still return zero and
the interpreter continues to report the exact number of traversed queries. -/
noncomputable def baseContinuousVolumeCooling
    (P : ContinuousVolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  (P.initialSample q).bind fun initialPoint =>
    match initialPoint with
    | none => .pure 0
    | some point =>
        (continuousCoolingProduct P q (S q).variances point).bind fun product =>
          match product with
          | none => .pure 0
          | some (gaussianProduct, lastPoint) =>
              (P.uniformRatioEstimate q (terminalVariance q) lastPoint).bind fun finalRatio =>
                .pure <| match finalRatio with
                  | some uniformRatio =>
                      initialGaussianIntegral q * gaussianProduct * uniformRatio
                  | none => 0

end ArlibCommunity.Algorithms.CV18
