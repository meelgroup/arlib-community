/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.TapeInterp

/-!
# The algorithm as tape programs

The procedures of `Model/Program.lean`, written as tape programs (`TapeProgram`), line
for line.  `interp` of each is the corresponding procedure of `Program`
(`ballWalkStep_interp`, …, `figureOneRun_interp`).
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.CV18

open ArlibCommunity.Algorithms.CV18.Model.Operations

namespace Tape

variable (q : VolumeParams)

noncomputable def ballWalkStep (sigma2 : ℝ) (x : AmbientSpace q.n) :
    TapeProgram q.n (Bool × AmbientSpace q.n) := do
  let u ← TapeProgram.ballPoint
  let y := x + proposalRadius q sigma2 • u
  let inside ← TapeProgram.isMember y
  let coin ← TapeProgram.unitNumber
  if inside = true ∧ ‖y‖ ≤ Real.sqrt (terminalVariance q) ∧
      ‖y‖ ≤ phaseRadius q sigma2 then
    pure (true, if coin ≤ lazyAcceptance sigma2 x y then y else x)
  else
    pure (false, x)

noncomputable def properWalk (sigma2 : ℝ) :
    (cap steps : ℕ) → AmbientSpace q.n → TapeProgram q.n (Option (AmbientSpace q.n))
  | 0, _, _ => pure none
  | _ + 1, 0, x => do
      let _ ← TapeProgram.isMember ((scaleFactor q)⁻¹ • x)
      pure (some x)
  | cap + 1, steps + 1, x => do
      let (proper, y) ← ballWalkStep q sigma2 x
      properWalk sigma2 cap (if proper then steps else steps + 1) y

noncomputable def rejectionAttempt (sigma2 : ℝ) (x : AmbientSpace q.n) :
    TapeProgram q.n (Bool × AmbientSpace q.n) := do
  let c := scaleFactor q
  let y := c⁻¹ • x
  let inside ← TapeProgram.isMember y
  let coin ← TapeProgram.unitNumber
  if inside = true ∧ ‖y‖ ≤ Real.sqrt (terminalVariance q) ∧
      ‖y‖ ≤ phaseRadius q sigma2 ∧
      ENNReal.ofReal coin ≤ (2 : ENNReal)⁻¹ * gaussianScaleAcceptance sigma2 c y then
    pure (true, y)
  else
    pure (false, y)

noncomputable def collectSamples (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (cap steps retries : ℕ) :
    (retriesLeft samplesLeft : ℕ) → (total : ℝ) → AmbientSpace q.n →
      TapeProgram q.n (Option (ℝ × AmbientSpace q.n))
  | _, 0, total, x => pure (some (total, x))
  | 0, _ + 1, _, _ => pure none
  | retriesLeft + 1, samplesLeft + 1, total, x => do
      let some y ← properWalk q sigma2 (cap + 1) steps x | pure none
      let (accepted, z) ← rejectionAttempt q sigma2 y
      if accepted then
        collectSamples sigma2 weight cap steps retries retries samplesLeft
          (total + weight z) y
      else
        collectSamples sigma2 weight cap steps retries retriesLeft
          (samplesLeft + 1) total y
termination_by retriesLeft samplesLeft => (samplesLeft, retriesLeft)

noncomputable def coolingPhase (sigma2 tau2 : ℝ) (x : AmbientSpace q.n) :
    TapeProgram q.n (Option (ℝ × AmbientSpace q.n)) := do
  let c := scaleFactor q
  let k := phaseSampleCount q sigma2
  let some (total, y) ← collectSamples q sigma2 (gaussianRatioWeight sigma2 tau2)
      (maxProposals q sigma2) (walkSteps q sigma2)
      (maxRetries q) (maxRetries q) k 0 (c • x)
    | pure none
  pure (some (total / k, c⁻¹ • y))

noncomputable def uniformPhase (sigma2 : ℝ) (x : AmbientSpace q.n) :
    TapeProgram q.n (Option ℝ) := do
  let c := scaleFactor q
  let k := sampleCount q
  let some (total, _) ← collectSamples q sigma2 (uniformRatioWeight sigma2)
      (maxProposals q sigma2) (walkSteps q sigma2)
      (maxRetries q) (maxRetries q) k 0 (c • x)
    | pure none
  pure (some (total / k))

noncomputable def initialSample : TapeProgram q.n (Option (AmbientSpace q.n)) := do
  let g ← TapeProgram.gaussianVector
  let x := Real.sqrt (initialVariance q) • g
  let inside ← TapeProgram.isMember x
  pure (if inside = true ∧ ‖x‖ ≤ Real.sqrt (terminalVariance q) then some x else none)

noncomputable def coolingPhases :
    List ℝ → AmbientSpace q.n → TapeProgram q.n (Option (ℝ × AmbientSpace q.n))
  | sigma2 :: tau2 :: rest, x => do
      let some (W, y) ← coolingPhase q sigma2 tau2 x | pure none
      let some (product, z) ← coolingPhases (tau2 :: rest) y | pure none
      pure (some (W * product, z))
  | _, x => pure (some (1, x))

noncomputable def figureOneRun : TapeProgram q.n ℝ := do
  let some x₀ ← initialSample q | pure 0
  let some (product, x) ← coolingPhases q (coolingSchedule q) x₀ | pure 0
  let some U ← uniformPhase q (terminalVariance q) x | pure 0
  pure (initialGaussianIntegral q * product * U)

/-- One run of Figure 1 with at most `queryBudget q` membership calls; a run that would
make more reports `0`. -/
noncomputable def cappedRun : TapeProgram q.n ℝ := do
  let r ← (figureOneRun q).withQueryCap (queryBudget q)
  pure (r.getD 0)

noncomputable def repeatIndependently {n : ℕ} (run : TapeProgram n ℝ) :
    (m : ℕ) → TapeProgram n (Fin m → ℝ)
  | 0 => pure Fin.elim0
  | m + 1 => do
      let first ← run
      let rest ← repeatIndependently run m
      pure (Fin.cons first rest)

noncomputable def medianOfRuns : TapeProgram q.n ℝ := do
  let estimates ← repeatIndependently (cappedRun q) (confidenceRepetitions q)
  pure (Arlib.Probability.medianOf estimates)

/-! ## The tape programs stand for the procedures of `Program` -/

open TapeProgram

theorem interp_ite {n : ℕ} {α : Type} (c : Prop) [Decidable c] (a b : TapeProgram n α) :
    interp (if c then a else b) = if c then interp a else interp b := by
  split <;> rfl

theorem ballWalkStep_interp (sigma2 : ℝ) (x : AmbientSpace q.n) :
    interp (ballWalkStep q sigma2 x) = Program.ballWalkStep q sigma2 x := by
  simp only [ballWalkStep, Program.ballWalkStep, interp_bind', interp_ballPoint,
    interp_isMember, interp_unitNumber, interp_ite, interp_pure']

theorem properWalk_interp (sigma2 : ℝ) :
    ∀ (cap steps : ℕ) (x : AmbientSpace q.n),
      interp (properWalk q sigma2 cap steps x) = Program.properWalk q sigma2 cap steps x
  | 0, _, _ => rfl
  | _ + 1, 0, x => by
      simp only [properWalk, Program.properWalk, interp_bind', interp_isMember, interp_pure']
  | cap + 1, steps + 1, x => by
      simp only [properWalk, Program.properWalk, interp_bind', ballWalkStep_interp]
      congr 1
      funext r
      rcases r with ⟨proper, y⟩
      exact properWalk_interp sigma2 cap _ y

theorem rejectionAttempt_interp (sigma2 : ℝ) (x : AmbientSpace q.n) :
    interp (rejectionAttempt q sigma2 x) = Program.rejectionAttempt q sigma2 x := by
  simp only [rejectionAttempt, Program.rejectionAttempt, interp_bind', interp_isMember,
    interp_unitNumber, interp_ite, interp_pure']

theorem collectSamples_interp (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (cap steps retries : ℕ) :
    ∀ (retriesLeft samplesLeft : ℕ) (total : ℝ) (x : AmbientSpace q.n),
      interp (collectSamples q sigma2 weight cap steps retries retriesLeft samplesLeft total x) =
        Program.collectSamples q sigma2 weight cap steps retries retriesLeft samplesLeft
          total x
  | _, 0, total, x => by
      rw [collectSamples, Program.collectSamples]
      rfl
  | 0, _ + 1, _, _ => by
      rw [collectSamples, Program.collectSamples]
      rfl
  | retriesLeft + 1, samplesLeft + 1, total, x => by
      rw [collectSamples, Program.collectSamples]
      simp only [interp_bind', properWalk_interp]
      congr 1
      funext o
      rcases o with _ | y
      · rfl
      · simp only [interp_bind', rejectionAttempt_interp]
        congr 1
        funext a
        rcases a with ⟨accepted, z⟩
        cases accepted
        · exact collectSamples_interp sigma2 weight cap steps retries retriesLeft
            (samplesLeft + 1) total y
        · exact collectSamples_interp sigma2 weight cap steps retries retries samplesLeft
            (total + weight z) y
termination_by retriesLeft samplesLeft => (samplesLeft, retriesLeft)

theorem coolingPhase_interp (sigma2 tau2 : ℝ) (x : AmbientSpace q.n) :
    interp (coolingPhase q sigma2 tau2 x) = Program.coolingPhase q sigma2 tau2 x := by
  simp only [coolingPhase, Program.coolingPhase, interp_bind', collectSamples_interp]
  congr 1
  funext o
  rcases o with _ | ⟨total, y⟩ <;> rfl

theorem uniformPhase_interp (sigma2 : ℝ) (x : AmbientSpace q.n) :
    interp (uniformPhase q sigma2 x) = Program.uniformPhase q sigma2 x := by
  simp only [uniformPhase, Program.uniformPhase, interp_bind', collectSamples_interp]
  congr 1
  funext o
  rcases o with _ | ⟨total, y⟩ <;> rfl

theorem initialSample_interp : interp (initialSample q) = Program.initialSample q := by
  simp only [initialSample, Program.initialSample, interp_bind', interp_gaussianVector,
    interp_isMember, interp_pure']

theorem coolingPhases_interp :
    ∀ (variances : List ℝ) (x : AmbientSpace q.n),
      interp (coolingPhases q variances x) = Program.coolingPhases q variances x
  | [], x => rfl
  | [_], x => rfl
  | sigma2 :: tau2 :: rest, x => by
      rw [coolingPhases, Program.coolingPhases]
      simp only [interp_bind', coolingPhase_interp]
      congr 1
      funext o
      rcases o with _ | ⟨W, y⟩
      · rfl
      · simp only [interp_bind', coolingPhases_interp (tau2 :: rest) y]
        congr 1
        funext o'
        rcases o' with _ | ⟨product, z⟩ <;> rfl

theorem figureOneRun_interp : interp (figureOneRun q) = Program.figureOneRun q := by
  simp only [figureOneRun, Program.figureOneRun, interp_bind', initialSample_interp]
  congr 1
  funext o
  rcases o with _ | x₀
  · rfl
  · simp only [interp_bind', coolingPhases_interp]
    congr 1
    funext o'
    rcases o' with _ | ⟨product, x⟩
    · rfl
    · simp only [interp_bind', uniformPhase_interp]
      congr 1
      funext o''
      rcases o'' with _ | U <;> rfl

end Tape

end ArlibCommunity.Algorithms.CV18
