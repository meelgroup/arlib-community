/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.TapeMeasurability

/-!
# The sampler as tape programs

The procedures of `Model/Program.lean`, written as tape programs line for line.  `interp`
of each is the corresponding procedure of `Program` (`step_interp`, `walk_interp`), and
each runs measurably when membership is answered measurably (`step_meas`, `walk_meas`).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Algorithms.HitAndRun.Model.Operations

namespace Tape

noncomputable def bisect {n : ℕ} (x θ : State n) : (k : ℕ) → (inner outer : ℝ) →
    TapeProgram n ℝ
  | 0, _, outer => pure outer
  | k + 1, inner, outer => do
      let mid := (inner + outer) / 2
      let inside ← TapeProgram.isMember (x + mid • θ)
      if inside then bisect x θ k mid outer else bisect x θ k inner mid

noncomputable def chordPoint {n : ℕ} (x θ : State n) (lo hi : ℝ) :
    (r : ℕ) → TapeProgram n (State n)
  | 0 => pure x
  | r + 1 => do
      let u ← TapeProgram.unitNumber
      let y := x + (-lo + u * (lo + hi)) • θ
      let inside ← TapeProgram.isMember y
      if inside then pure y else chordPoint x θ lo hi r

noncomputable def step {n : ℕ} (w : WalkParams) (x : State n) : TapeProgram n (State n) := do
  let coin ← TapeProgram.unitNumber
  if coin ≤ 1 / 2 then pure x else do
    let g ← TapeProgram.gaussianVector
    let θ := ‖g‖⁻¹ • g
    let hi ← bisect x θ w.bisectionSteps 0 (2 * w.D)
    let lo ← bisect x (-θ) w.bisectionSteps 0 (2 * w.D)
    chordPoint x θ lo hi w.rejectionTries

noncomputable def walk {n : ℕ} (w : WalkParams) : (m : ℕ) → State n → TapeProgram n (State n)
  | 0, x => pure x
  | m + 1, x => do
      let y ← step w x
      walk w m y

/-! ## The tape programs stand for the procedures of `Program` -/

open TapeProgram

variable {n : ℕ}

theorem bisect_interp (x θ : State n) :
    ∀ (k : ℕ) (inner outer : ℝ), interp (bisect x θ k inner outer) =
      Program.bisect x θ k inner outer
  | 0, _, _ => rfl
  | k + 1, inner, outer => by
      simp only [bisect, Program.bisect, interp_bind', interp_isMember, interp_ite,
        bisect_interp x θ k]

theorem chordPoint_interp (x θ : State n) (lo hi : ℝ) :
    ∀ r : ℕ, interp (chordPoint x θ lo hi r) = Program.chordPoint x θ lo hi r
  | 0 => rfl
  | r + 1 => by
      simp only [chordPoint, Program.chordPoint, interp_bind', interp_unitNumber,
        interp_isMember, interp_ite, interp_pure', chordPoint_interp x θ lo hi r]

theorem step_interp (w : WalkParams) (x : State n) :
    interp (step w x) = Program.step w x := by
  simp only [step, Program.step, interp_bind', interp_unitNumber, interp_ite, interp_pure',
    interp_gaussianVector, bisect_interp, chordPoint_interp]

theorem walk_interp (w : WalkParams) :
    ∀ (m : ℕ) (x : State n), interp (walk w m x) = Program.walk w m x
  | 0, _ => rfl
  | m + 1, x => by
      simp only [walk, Program.walk, interp_bind', step_interp, walk_interp w m]

/-! ## The tape programs run measurably -/

variable {member : State n → Bool} (hm : Measurable member)
include hm

theorem bisect_meas :
    ∀ k : ℕ, MeasFam member fun q : (State n × State n) × ℝ × ℝ =>
      bisect q.1.1 q.1.2 k q.2.1 q.2.2
  | 0 => MeasFam.congr (MeasFam.pure (g := fun q : (State n × State n) × ℝ × ℝ => q.2.2)
      (by fun_prop)) fun _ => rfl
  | k + 1 => by
      refine MeasFam.bindIsMember hm (x := fun q : (State n × State n) × ℝ × ℝ =>
        q.1.1 + ((q.2.1 + q.2.2) / 2) • q.1.2) (by fun_prop) ?_
      refine MeasFam.ite (measurable_snd (measurableSet_singleton true)) ?_ ?_
      · exact (bisect_meas k).comp (φ := fun q : ((State n × State n) × ℝ × ℝ) × Bool =>
          (q.1.1, ((q.1.2.1 + q.1.2.2) / 2, q.1.2.2))) (by fun_prop)
      · exact (bisect_meas k).comp (φ := fun q : ((State n × State n) × ℝ × ℝ) × Bool =>
          (q.1.1, (q.1.2.1, (q.1.2.1 + q.1.2.2) / 2))) (by fun_prop)

theorem chordPoint_meas :
    ∀ r : ℕ, MeasFam member fun q : (State n × State n) × ℝ × ℝ =>
      chordPoint q.1.1 q.1.2 q.2.1 q.2.2 r
  | 0 => MeasFam.congr (MeasFam.pure (g := fun q : (State n × State n) × ℝ × ℝ => q.1.1)
      (by fun_prop)) fun _ => rfl
  | r + 1 => by
      refine MeasFam.bindUnit ?_
      refine MeasFam.bindIsMember hm (x := fun q : ((State n × State n) × ℝ × ℝ) × ℝ =>
        q.1.1.1 + (-q.1.2.1 + q.2 * (q.1.2.1 + q.1.2.2)) • q.1.1.2) (by fun_prop) ?_
      refine MeasFam.ite (measurable_snd (measurableSet_singleton true)) ?_ ?_
      · exact MeasFam.pure (g := fun q : (((State n × State n) × ℝ × ℝ) × ℝ) × Bool =>
          q.1.1.1.1 + (-q.1.1.2.1 + q.1.2 * (q.1.1.2.1 + q.1.1.2.2)) • q.1.1.1.2)
          (by fun_prop)
      · exact (chordPoint_meas r).comp (φ := fun q : (((State n × State n) × ℝ × ℝ) × ℝ) ×
          Bool => q.1.1) (by fun_prop)

theorem step_meas (w : WalkParams) : MeasFam member fun x : State n => step w x := by
  refine MeasFam.bindUnit ?_
  refine MeasFam.ite (measurableSet_le measurable_snd measurable_const)
    (MeasFam.pure (g := fun q : State n × ℝ => q.1) measurable_fst) ?_
  refine MeasFam.bindGaussian ?_
  have hθ : Measurable fun q : (State n × ℝ) × State n => ‖q.2‖⁻¹ • q.2 := by fun_prop
  refine MeasFam.bind' ((bisect_meas hm w.bisectionSteps).comp
    (φ := fun q : (State n × ℝ) × State n => ((q.1.1, ‖q.2‖⁻¹ • q.2), ((0 : ℝ), 2 * w.D)))
    (by fun_prop)) ?_
  refine MeasFam.bind' ((bisect_meas hm w.bisectionSteps).comp
    (φ := fun q : ((State n × ℝ) × State n) × ℝ =>
      ((q.1.1.1, -(‖q.1.2‖⁻¹ • q.1.2)), ((0 : ℝ), 2 * w.D))) (by fun_prop)) ?_
  exact (chordPoint_meas hm w.rejectionTries).comp
    (φ := fun q : (((State n × ℝ) × State n) × ℝ) × ℝ =>
      ((q.1.1.1.1, ‖q.1.1.2‖⁻¹ • q.1.1.2), (q.2, q.1.2))) (by fun_prop)

theorem walk_meas (w : WalkParams) :
    ∀ m : ℕ, MeasFam member fun x : State n => walk w m x
  | 0 => MeasFam.congr (MeasFam.pure (g := fun x : State n => x) measurable_id) fun _ => rfl
  | m + 1 => by
      exact MeasFam.congr (MeasFam.bind' (h := fun _ y => walk w m y) (step_meas hm w)
        ((walk_meas w m).comp (φ := fun q : State n × State n => q.2) measurable_snd))
        fun x => rfl

end Tape

end ArlibCommunity.Algorithms.HitAndRun
