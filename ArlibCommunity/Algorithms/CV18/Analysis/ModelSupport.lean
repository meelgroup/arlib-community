/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Pseudocode

/-!
# Model-adjacent definitions used only by the analysis

These declarations used to live under `Model/` but are not reached by the
statement of Theorem 1.1, so they are not part of the audit surface: the
`Option` measurable structure, Gaussian-ratio helpers, interpretation with an
explicit query counter (`MembershipOracleProgram.run`), the syntax-level
`QueryBound` certificate, the truncated body, and the general Figure 1
skeleton over an arbitrary proof-carrying schedule.
-/

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-! ## Measurable structure on `Option` -/

/-- The usual disjoint-union measurable structure on `Option`. -/
def optionToSum {α : Type*} : Option α → Sum Unit α
  | none => Sum.inl ()
  | some value => Sum.inr value

@[instance_reducible] def optionMeasurableSpace
    {α : Type*} [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap optionToSum inferInstance

instance {α : Type*} [MeasurableSpace α] : MeasurableSpace (Option α) :=
  optionMeasurableSpace

theorem measurable_some {α : Type*} [MeasurableSpace α] :
    Measurable (some : α → Option α) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap some optionMeasurableSpace ≤ _
  unfold optionMeasurableSpace
  rw [MeasurableSpace.comap_comp]
  exact measurable_inr.comap_le

theorem measurable_optionToSum {α : Type*} [MeasurableSpace α] :
    Measurable (optionToSum : Option α → Sum Unit α) := by
  rw [measurable_iff_comap_le]
  exact le_rfl

theorem Measurable.optionElim {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (noneValue : β)
    {someValue : α → β} (hsome : Measurable someValue) :
    Measurable fun value : Option α =>
      match value with
      | none => noneValue
      | some x => someValue x := by
  rw [show (fun value : Option α =>
      match value with
      | none => noneValue
      | some x => someValue x) =
      Sum.elim (fun _ : Unit => noneValue) someValue ∘ optionToSum by
    funext value
    cases value <;> rfl]
  exact (measurable_const.sumElim hsome).comp measurable_optionToSum

theorem measurable_optionIsSome {α : Type*} [MeasurableSpace α] :
    Measurable (Option.isSome : Option α → Bool) := by
  convert (Measurable.optionElim false
    (someValue := fun _ : α => true) measurable_const) using 1
  funext value
  cases value <;> rfl

theorem measurable_optionGetD {α : Type*} [MeasurableSpace α]
    (default : α) : Measurable fun value : Option α => value.getD default := by
  convert (Measurable.optionElim default (someValue := id) measurable_id) using 1
  funext value
  cases value <;> rfl

/-- Measurability of a parameterized case split on an optional value. -/
theorem Measurable.optionCases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (default : α) {noneValue : γ → β} {someValue : γ × α → β}
    (hnone : Measurable noneValue) (hsome : Measurable someValue) :
    Measurable fun p : γ × Option α =>
      match p.2 with
      | none => noneValue p.1
      | some value => someValue (p.1, value) := by
  have hif : Measurable fun p : γ × Option α =>
      if p.2.isSome then
        someValue (p.1, p.2.getD default)
      else noneValue p.1 := by
    apply Measurable.ite
    · exact (measurable_optionIsSome.comp measurable_snd)
        (measurableSet_singleton true)
    · exact hsome.comp (measurable_fst.prodMk
        (measurable_optionGetD default |>.comp measurable_snd))
    · exact hnone.comp measurable_fst
  convert hif using 1
  funext p
  cases p.2 <;> rfl

/-! ## Unnormalised Gaussian bridge used by Figure 1 -/

/-- The unnormalised Gaussian weight restricted to a measurable set. This is
an ordinary real-valued density function, not Mathlib's standard-Gaussian
probability measure. -/
noncomputable def unnormGaussian {n : ℕ} (K : Set (AmbientSpace n))
    (sigma2 : ℝ) (x : AmbientSpace n) : ℝ :=
  K.indicator (fun y => Real.exp (-‖y‖ ^ 2 / (2 * sigma2))) x

/-- The partition function whose adjacent ratios telescope in Figure 1. -/
noncomputable def gaussianIntegral {n : ℕ} (K : Set (AmbientSpace n))
    (sigma2 : ℝ) : ℝ :=
  ∫ x, unnormGaussian K sigma2 x

/-- Importance weight from variance `sigma2` to the larger variance `tau2`. -/
noncomputable def gaussianRatioSample {n : ℕ} (K : Set (AmbientSpace n))
    (sigma2 tau2 : ℝ) (x : AmbientSpace n) : ℝ :=
  unnormGaussian K tau2 x / unnormGaussian K sigma2 x

/-- Importance weight for the final transition from a Gaussian density to the
uniform density on the same truncated body. -/
noncomputable def uniformRatioSample {n : ℕ} (K : Set (AmbientSpace n))
    (sigma2 : ℝ) (x : AmbientSpace n) : ℝ :=
  K.indicator (fun y => Real.exp (‖y‖ ^ 2 / (2 * sigma2))) x

/-! ## Legacy rate -/

/-- The general well-rounded rate after median confidence amplification. -/
noncomputable def volumeComplexityRate (q : VolumeParams) : ℝ :=
  volumeBaseComplexityRate q * protectedLog (1 / q.p)

/-! ## Execution with query counts and the syntax-level query bound -/

/-- Execute a program against an oracle. The second component is the actual
number of `query` nodes traversed by that execution. -/
noncomputable def MembershipOracleProgram.run {n : ℕ} {Result : Type}
    [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool) :
    MembershipOracleProgram n Result → Measure (Result × ℕ)
  | .pure result => Measure.dirac (result, 0)
  | .query point next =>
      (run oracle (next (oracle point))).map fun outcome =>
        (outcome.1, outcome.2 + 1)
  | .randomNat law next => law.toMeasure.bind fun seed => run oracle (next seed)
  | .randomPoint law _ next => law.bind fun point => run oracle (next point)
  | .randomReal law _ next => law.bind fun value => run oracle (next value)

/-- A syntax-level worst-case membership-query bound. Continuous draws do not
hide a cost field: every possible continuation must satisfy the same bound. -/
inductive MembershipOracleProgram.QueryBound {n : ℕ} {Result : Type} :
    MembershipOracleProgram n Result → ℕ → Prop where
  | pure (result : Result) (budget : ℕ) : QueryBound (.pure result) budget
  | query (point : AmbientSpace n) (next : Bool → MembershipOracleProgram n Result)
      (budget : ℕ) (hnext : ∀ answer, QueryBound (next answer) budget) :
      QueryBound (.query point next) (budget + 1)
  | randomNat (law : PMF ℕ) (next : ℕ → MembershipOracleProgram n Result)
      (budget : ℕ) (hnext : ∀ seed, QueryBound (next seed) budget) :
      QueryBound (.randomNat law next) budget
  | randomPoint (law : Measure (AmbientSpace n)) (hprob : IsProbabilityMeasure law)
      (next : AmbientSpace n → MembershipOracleProgram n Result)
      (budget : ℕ) (hnext : ∀ point, QueryBound (next point) budget) :
      QueryBound (.randomPoint law hprob next) budget
  | randomReal (law : Measure ℝ) (hprob : IsProbabilityMeasure law)
      (next : ℝ → MembershipOracleProgram n Result)
      (budget : ℕ) (hnext : ∀ value, QueryBound (next value) budget) :
      QueryBound (.randomReal law hprob next) budget

/-- The syntax-directed bound controls the charged cost from every draw index. -/
theorem MembershipOracleProgram.QueryBound.toMembershipCostBoundFrom
    {n : ℕ} {Result : Type} {program : MembershipOracleProgram n Result}
    {budget : ℕ} (h : program.QueryBound budget) :
    ∀ (drawIndex : ℕ) (oracle : AmbientSpace n → Bool)
      (choices : MembershipCostChoices n),
      Arlib.Computation.Charged.steps
        (Arlib.Computation.Rate.unit Arlib.Computation.StdOp)
        (chargedMembershipRunFrom oracle choices drawIndex program) ≤ budget := by
  induction h with
  | pure result budget =>
      intro drawIndex oracle choices
      simp only [chargedMembershipRunFrom]
      exact (Arlib.Computation.Charged.steps_pure _ result).trans_le (Nat.zero_le budget)
  | query point next budget hnext ih =>
      intro drawIndex oracle choices
      simp only [chargedMembershipRunFrom, Arlib.Computation.Charged.steps_bind,
        Arlib.Computation.Charged.steps_op, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Rate.unit_cost]
      have htail := ih (oracle point) drawIndex oracle choices
      omega
  | randomNat law next budget hnext ih =>
      intro drawIndex oracle choices
      simp only [chargedMembershipRunFrom]
      exact ih (choices.randomNat drawIndex law) (drawIndex + 1) oracle choices
  | randomPoint law hprob next budget hnext ih =>
      intro drawIndex oracle choices
      simp only [chargedMembershipRunFrom]
      exact ih (choices.randomPoint drawIndex law) (drawIndex + 1) oracle choices
  | randomReal law hprob next budget hnext ih =>
      intro drawIndex oracle choices
      simp only [chargedMembershipRunFrom]
      exact ih (choices.randomReal drawIndex law) (drawIndex + 1) oracle choices

/-- The existing syntax-directed bound is a certificate for the cost derived
from Arlib's charged roster-membership operation. -/
theorem MembershipOracleProgram.QueryBound.toMembershipCostBound
    {n : ℕ} {Result : Type} {program : MembershipOracleProgram n Result}
    {budget : ℕ} (h : program.QueryBound budget) :
    program.MembershipCostBound budget := by
  intro oracle choices
  exact h.toMembershipCostBoundFrom 0 oracle choices

/-! ## Truncated body and the general Figure 1 skeleton -/

/-- The high-probability truncation of `K` used to turn the second-moment
promise into the outer-radius hypothesis required by Figure 1. -/
noncomputable def truncatedBody (q : VolumeParams) (I : VolumeInput q.n) :
    Set (AmbientSpace q.n) :=
  (I.body : Set (AmbientSpace q.n)) ∩ Metric.closedBall 0 (Real.sqrt (terminalVariance q))

/-- A finite schedule witnessing the loop in Figure 1.

Existence and quantitative bounds for this schedule are analysis obligations;
they are deliberately not hidden inside an unconstrained estimator. -/
structure VolumeCoolingSchedule (q : VolumeParams) where
  variances : List ℝ
  nonempty : variances ≠ []
  start : variances.head? = some (initialVariance q)
  step : variances.IsChain (fun sigma2 tau2 => tau2 = nextVariance q sigma2)
  positive : ∀ sigma2 ∈ variances, 0 < sigma2
  finish : variances.getLast? = some (terminalVariance q)

/-- `baseVolumeCoolingOn` along a proof-carrying schedule.  The general
analysis is phrased for an arbitrary `VolumeCoolingSchedule`. -/
noncomputable def baseVolumeCooling (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) : MembershipOracleProgram q.n ℝ :=
  (P.initialSample q).bind fun initialPoint =>
    match initialPoint with
    | none => .pure 0
    | some point =>
        (coolingProduct P q (S q).variances point).bind fun product =>
          match product with
          | none => .pure 0
          | some (gaussianProduct, lastPoint) =>
              (P.uniformRatioEstimate q (terminalVariance q) lastPoint).bind fun finalRatio =>
                .pure <| match finalRatio with
                  | some uniformRatio =>
                      initialGaussianIntegral q * gaussianProduct * uniformRatio
                  | none => 0

/-- Repeat a program independently in the `PMF` semantics. -/
noncomputable def repeatVolumeCooling (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q)
    (q : VolumeParams) : (m : ℕ) → MembershipOracleProgram q.n (Fin m → ℝ)
  | 0 => .pure Fin.elim0
  | m + 1 =>
      (baseVolumeCooling P S q).bind fun estimate =>
        (repeatVolumeCooling P S q m).bind fun tail =>
          .pure (Fin.cons estimate tail)

/-- The shape of the paper's volume algorithm for arbitrary primitives:
repeated cooling runs followed by their median.  The certified algorithm is
`cv18Program` below, which additionally guards every base
run with a global query budget. -/
noncomputable def volumeCoolingAlgorithm (P : VolumeCoolingPrimitives)
    (S : (q : VolumeParams) → VolumeCoolingSchedule q) : VolumeAlgorithm :=
  fun q =>
    (repeatVolumeCooling P S q (confidenceRepetitions q)).bind fun estimates =>
      .pure (Arlib.Probability.medianOf estimates)

end ArlibCommunity.Algorithms.CV18
