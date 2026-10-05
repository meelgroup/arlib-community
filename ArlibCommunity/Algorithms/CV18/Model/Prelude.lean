/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Prelude
import ArlibCommunity.Algorithms.CV18.Meta.ModelClosure
import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Ordinary-volume model

The audit surface for the paper's theorem `thm:volume`. In particular, the
target below is Lebesgue volume; this development no longer defines its target
through Mathlib's standard Gaussian probability measure.
-/

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

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

/-! ## Inputs and target -/

/-- The paper's ambient Euclidean space `ℝⁿ`. -/
abbrev AmbientSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Numerical parameters for the general `R²` form stated immediately after
`thm:volume`. `roundness` is the dimension-free factor in
`E_K ‖X‖² ≤ roundness * n`; setting it to a universal constant gives the
headline well-rounded `O*(n³)` theorem. -/
structure VolumeParams where
  n : ℕ
  /-- The paper's fixed-variance lemma assumes `n ≥ 3`. Low dimensions must
  eventually be discharged by a separate branch. -/
  dim_ok : 3 ≤ n
  eps : ℝ
  heps : eps ∈ Set.Ioo 0 1
  p : ℝ
  hp : p ∈ Set.Ioo 0 1
  roundness : ℝ
  roundness_pos : 0 < roundness

/-- The centered closed Euclidean unit ball. -/
def unitBall (n : ℕ) : Set (AmbientSpace n) := Metric.closedBall 0 1

/-- A compact convex body containing the known centered unit ball.

Using `ConvexBody` records the boundedness and nonemptiness implicit in the
paper's phrase "convex body". -/
structure VolumeInput (n : ℕ) where
  body : ConvexBody (AmbientSpace n)
  unitBall_subset : unitBall n ⊆ (body : Set (AmbientSpace n))

/-- Exact black-box membership access to the body. -/
structure MembershipOracle {n : ℕ} (I : VolumeInput n) where
  query : AmbientSpace n → Bool
  correct : ∀ x, query x = true ↔ x ∈ (I.body : Set (AmbientSpace n))

/-- The ordinary Lebesgue volume targeted by `thm:volume`. -/
noncomputable def euclideanVolume {n : ℕ} (I : VolumeInput n) : ℝ :=
  (volume (I.body : Set (AmbientSpace n))).toReal

/-- The uniform second moment `E_K ‖X‖²`, written as a ratio of Lebesgue
integrals so that it does not depend on a Gaussian measure. -/
noncomputable def uniformSecondMoment {n : ℕ} (I : VolumeInput n) : ℝ :=
  (∫ x in (I.body : Set (AmbientSpace n)), ‖x‖ ^ 2) / euclideanVolume I

/-- The explicit well-roundedness promise supplied to the algorithm. -/
def WellRounded (q : VolumeParams) (I : VolumeInput q.n) : Prop :=
  uniformSecondMoment I ≤ q.roundness * (q.n : ℝ)

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

/-- A returned estimate together with the number of membership queries
actually taken by its execution. -/
structure VolumeRun where
  estimate : ℝ
  oracleCalls : ℕ

instance : MeasurableSpace VolumeRun :=
  MeasurableSpace.comap (fun run : VolumeRun => (run.estimate, run.oracleCalls)) inferInstance

/-- Relative accuracy in the paper's `(1 ± ε)` convention. -/
def RelativeApprox (ε target estimate : ℝ) : Prop :=
  estimate ∈ Arlib.relErr ε target

/-! ## Oracle-only randomized programs -/

/-- A finite membership-oracle program with both discrete and genuine
continuous internal randomness. A program is selected before the body and
oracle are quantified and can observe the body only through `query` nodes. -/
inductive MembershipOracleProgram (n : ℕ) (Result : Type) where
  | pure (result : Result)
  | query (point : AmbientSpace n) (next : Bool → MembershipOracleProgram n Result)
  | randomNat (law : PMF ℕ) (next : ℕ → MembershipOracleProgram n Result)
  | randomPoint (law : Measure (AmbientSpace n))
      (lawProbability : IsProbabilityMeasure law)
      (next : AmbientSpace n → MembershipOracleProgram n Result)
  | randomReal (law : Measure ℝ) (lawProbability : IsProbabilityMeasure law)
      (next : ℝ → MembershipOracleProgram n Result)

/-- A uniform randomized membership-oracle algorithm for ordinary volume. -/
abbrev VolumeAlgorithm := (q : VolumeParams) → MembershipOracleProgram q.n ℝ

/-- A logarithm protected below by one. This is the conventional meaning of
the displayed logarithmic complexity factors near parameter boundaries. -/
noncomputable def protectedLog (x : ℝ) : ℝ := max 1 (Real.log x)

/-- The variance scale at which the final Gaussian-to-uniform transition is
made.  Naming it here lets the exact query rate expose its logarithm. -/
noncomputable def volumeTerminalScale (q : VolumeParams) : ℝ :=
  max 1 (max (q.n : ℝ)
    (1024 * q.roundness * (q.n : ℝ) * protectedLog (8 / q.eps) ^ 2))

/-- Query rate of one constant-success run. Figure 1 uses `log(C² n)` both in
its sample count and in summing the accelerated phases. The paper replaces it
by `log n` after imposing polynomial parameter bounds; the exact unrestricted
formal statement retains the terminal scale. -/
noncomputable def volumeBaseComplexityRate (q : VolumeParams) : ℝ :=
  max 1 q.roundness * (q.n : ℝ) ^ 3 / q.eps ^ 2 *
    protectedLog (1 / q.eps) ^ 2 *
    protectedLog ((q.n : ℝ) / q.eps) ^ 2 *
    protectedLog (volumeTerminalScale q) ^ 2

/-- The general well-rounded rate after median confidence amplification. -/
noncomputable def volumeComplexityRate (q : VolumeParams) : ℝ :=
  volumeBaseComplexityRate q * protectedLog (1 / q.p)

end ArlibCommunity.Algorithms.CV18
