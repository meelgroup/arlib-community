/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.TapeAlgorithm
import ArlibCommunity.Algorithms.CV18.Analysis.TapeDrawLaws
import ArlibCommunity.Algorithms.CV18.Analysis.PseudocodeBridge
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduleTargetedKLS

/-!
# The tape algorithm refines the program tree

`toOP (Tape.medianOfRuns q)`, the tape algorithm with each random number drawn from its
law, is the program tree `cv18Program q` of `Analysis/OracleProgram.lean` with its two
kinds of point draw replaced by draws of random numbers pushed through arithmetic
(`cv18Program_refines`):

* the ball-walk proposal `uniformBall n x r` by `x + r · u`, `u` uniform on the unit
  ball (`uniformBall_eq_map`, for `r = proposalRadius q σ² > 0`);
* the starting point `initialGaussianLaw q` by `√σ₀² · g`, `g` a standard Gaussian
  vector (`initialGaussianLaw_eq_map`).
-/

set_option autoImplicit false

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

open TapeProgram

namespace TapeProgram

variable {n : ℕ} {α β : Type}

@[simp] theorem toOP_bind' (p : TapeProgram n α) (f : α → TapeProgram n β) :
    toOP (p >>= f) = (toOP p).bind fun a => toOP (f a) := toOP_bind p f

@[simp] theorem toOP_pure' (a : α) : toOP (Pure.pure a : TapeProgram n α) = .pure a := rfl

@[simp] theorem toOP_isMember (x : AmbientSpace n) :
    toOP (TapeProgram.isMember x) = CV18.isMember x := rfl

@[simp] theorem toOP_unitNumber : toOP (TapeProgram.unitNumber (n := n)) = drawReal uniformUnit :=
  rfl

theorem toOP_ite (c : Prop) [Decidable c] (a b : TapeProgram n α) :
    toOP (if c then a else b) = if c then toOP a else toOP b := by
  split <;> rfl

end TapeProgram

namespace Tape

variable (q : VolumeParams)

instance : NeZero q.n := ⟨by have := q.dim_ok; omega⟩

theorem ballWalkStep_refines {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (x : AmbientSpace q.n) :
    Refines (CV18.ballWalkStep q sigma2 x) (toOP (ballWalkStep q sigma2 x)) := by
  let K' : AmbientSpace q.n → MembershipOracleProgram q.n (Bool × AmbientSpace q.n) :=
    fun y => toOP (do
      let inside ← TapeProgram.isMember y
      let coin ← TapeProgram.unitNumber
      if inside = true ∧ ‖y‖ ≤ Real.sqrt (terminalVariance q) ∧
          ‖y‖ ≤ phaseRadius q sigma2 then
        Pure.pure (true, if coin ≤ lazyAcceptance sigma2 x y then y else x)
      else
        Pure.pure (false, x))
  have hK : ∀ y, Refines (MembershipOracleProgram.bind (CV18.isMember y) fun inside =>
      MembershipOracleProgram.bind (drawReal uniformUnit) fun coin =>
        if inside = true ∧ ‖y‖ ≤ Real.sqrt (terminalVariance q) ∧
            ‖y‖ ≤ phaseRadius q sigma2 then
          MembershipOracleProgram.pure (true, if coin ≤ lazyAcceptance sigma2 x y then y else x)
        else MembershipOracleProgram.pure (false, x)) (K' y) := by
    intro y
    refine Refines.query y fun inside => Refines.randomReal _ _ fun coin => ?_
    show Refines _ (toOP ((TapeProgram.pure coin).bind _))
    rw [TapeProgram.pure_bind, toOP_ite]
    exact Refines.refl _
  exact Refines.push _ _ _ _ (fun u => x + proposalRadius q sigma2 • u) (by fun_prop)
    (uniformBall_eq_map x (proposalRadius_pos q hsigma2)) hK

theorem rejectionAttempt_toOP (sigma2 : ℝ) (x : AmbientSpace q.n) :
    toOP (rejectionAttempt q sigma2 x) = CV18.rejectionAttempt q sigma2 x := by
  simp only [rejectionAttempt, CV18.rejectionAttempt, toOP_bind', toOP_isMember,
    toOP_unitNumber, toOP_ite, toOP_pure', bind_eq, pure_eq]

theorem properWalk_refines {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    ∀ (cap steps : ℕ) (x : AmbientSpace q.n),
      Refines (CV18.properWalk q sigma2 cap steps x) (toOP (properWalk q sigma2 cap steps x))
  | 0, _, _ => Refines.refl _
  | _ + 1, 0, x => by
      simp only [properWalk, CV18.properWalk, toOP_bind', toOP_isMember, toOP_pure', bind_eq,
        pure_eq]
      exact Refines.refl _
  | cap + 1, steps + 1, x => by
      simp only [properWalk, CV18.properWalk, toOP_bind', bind_eq]
      refine Refines.bind (ballWalkStep_refines q hsigma2 x) fun r => ?_
      rcases r with ⟨proper, y⟩
      exact properWalk_refines hsigma2 cap _ y

theorem collectSamples_refines {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (weight : AmbientSpace q.n → ℝ) (cap steps retries : ℕ) :
    ∀ (retriesLeft samplesLeft : ℕ) (total : ℝ) (x : AmbientSpace q.n),
      Refines (CV18.collectSamples q sigma2 weight cap steps retries retriesLeft samplesLeft
          total x)
        (toOP (collectSamples q sigma2 weight cap steps retries retriesLeft samplesLeft
          total x))
  | _, 0, total, x => by
      rw [collectSamples, CV18.collectSamples]
      exact Refines.refl _
  | 0, _ + 1, _, _ => by
      rw [collectSamples, CV18.collectSamples]
      exact Refines.refl _
  | retriesLeft + 1, samplesLeft + 1, total, x => by
      rw [collectSamples, CV18.collectSamples]
      simp only [toOP_bind', bind_eq]
      refine Refines.bind (properWalk_refines q hsigma2 _ _ x) fun o => ?_
      rcases o with _ | y
      · exact Refines.refl _
      · simp only [toOP_bind', rejectionAttempt_toOP]
        refine Refines.bind (Refines.refl _) fun a => ?_
        rcases a with ⟨accepted, z⟩
        cases accepted
        · exact collectSamples_refines hsigma2 weight cap steps retries retriesLeft
            (samplesLeft + 1) total y
        · exact collectSamples_refines hsigma2 weight cap steps retries retries samplesLeft
            (total + weight z) y
termination_by retriesLeft samplesLeft => (samplesLeft, retriesLeft)

theorem coolingPhase_refines {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (tau2 : ℝ)
    (x : AmbientSpace q.n) :
    Refines (CV18.coolingPhase q sigma2 tau2 x) (toOP (coolingPhase q sigma2 tau2 x)) := by
  simp only [coolingPhase, CV18.coolingPhase, toOP_bind', bind_eq]
  refine Refines.bind (collectSamples_refines q hsigma2 _ _ _ _ _ _ _ _) fun o => ?_
  rcases o with _ | ⟨total, y⟩ <;> exact Refines.refl _

theorem uniformPhase_refines {sigma2 : ℝ} (hsigma2 : 0 < sigma2) (x : AmbientSpace q.n) :
    Refines (CV18.uniformPhase q sigma2 x) (toOP (uniformPhase q sigma2 x)) := by
  simp only [uniformPhase, CV18.uniformPhase, toOP_bind', bind_eq]
  refine Refines.bind (collectSamples_refines q hsigma2 _ _ _ _ _ _ _ _) fun o => ?_
  rcases o with _ | ⟨total, y⟩ <;> exact Refines.refl _

theorem initialSample_refines :
    Refines (CV18.initialSample q) (toOP (initialSample q)) := by
  let K' : AmbientSpace q.n → MembershipOracleProgram q.n (Option (AmbientSpace q.n)) :=
    fun x => toOP (do
      let inside ← TapeProgram.isMember x
      Pure.pure (if inside = true ∧ ‖x‖ ≤ Real.sqrt (terminalVariance q) then some x
        else none))
  have hK : ∀ x, Refines (MembershipOracleProgram.bind (CV18.isMember x) fun inside =>
      MembershipOracleProgram.pure
        (if inside = true ∧ ‖x‖ ≤ Real.sqrt (terminalVariance q) then some x else none))
      (K' x) := fun x => Refines.refl _
  exact Refines.push _ _ _ _ (fun g => Real.sqrt (initialVariance q) • g) (by fun_prop)
    (initialGaussianLaw_eq_map q) hK

theorem coolingPhases_refines :
    ∀ (variances : List ℝ), (∀ v ∈ variances, 0 < v) → ∀ (x : AmbientSpace q.n),
      Refines (CV18.coolingPhases q variances x) (toOP (coolingPhases q variances x))
  | [], _, x => Refines.refl _
  | [_], _, x => Refines.refl _
  | sigma2 :: tau2 :: rest, hpos, x => by
      rw [coolingPhases, CV18.coolingPhases]
      simp only [toOP_bind', bind_eq]
      refine Refines.bind (coolingPhase_refines q (hpos sigma2 (by simp)) tau2 x) fun o => ?_
      rcases o with _ | ⟨W, y⟩
      · exact Refines.refl _
      · simp only [toOP_bind']
        refine Refines.bind (coolingPhases_refines (tau2 :: rest)
          (fun v hv => hpos v (List.mem_cons_of_mem _ hv)) y) fun o' => ?_
        rcases o' with _ | ⟨product, z⟩ <;> exact Refines.refl _

theorem figureOneRun_refines :
    Refines (CV18.figureOneRun q) (toOP (figureOneRun q)) := by
  have hpos : ∀ v ∈ coolingSchedule q, 0 < v := by
    intro v hv
    simp only [coolingSchedule, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact scheduleValue_pos q i
  simp only [figureOneRun, CV18.figureOneRun, toOP_bind', bind_eq]
  refine Refines.bind (initialSample_refines q) fun o => ?_
  rcases o with _ | x₀
  · exact Refines.refl _
  · simp only [toOP_bind']
    refine Refines.bind (coolingPhases_refines q _ hpos x₀) fun o' => ?_
    rcases o' with _ | ⟨product, x⟩
    · exact Refines.refl _
    · simp only [toOP_bind']
      refine Refines.bind (uniformPhase_refines q (terminalVariance_pos' q) x) fun o'' => ?_
      rcases o'' with _ | U <;> exact Refines.refl _

theorem cappedRun_refines : Refines (CV18.cappedRun q) (toOP (cappedRun q)) := by
  simp only [cappedRun, CV18.cappedRun, toOP_bind', bind_eq, toOP_withQueryCap]
  exact Refines.bind (Refines.withQueryCap (figureOneRun_refines q) _) fun _ => Refines.refl _

theorem repeatIndependently_refines {A : MembershipOracleProgram q.n ℝ}
    {B : TapeProgram q.n ℝ} (h : Refines A B.toOP) :
    ∀ m : ℕ, Refines (CV18.repeatIndependently A m) (toOP (repeatIndependently B m))
  | 0 => Refines.refl _
  | m + 1 => by
      simp only [repeatIndependently, CV18.repeatIndependently, toOP_bind', bind_eq]
      exact Refines.bind h fun first =>
        Refines.bind (repeatIndependently_refines h m) fun _ => Refines.refl _

/-- **The tape algorithm refines the program tree** `cv18Program q`. -/
theorem medianOfRuns_refines : Refines (cv18Program q) (toOP (medianOfRuns q)) := by
  simp only [medianOfRuns, cv18Program, toOP_bind', bind_eq]
  exact Refines.bind (repeatIndependently_refines q (cappedRun_refines q) _)
    fun _ => Refines.refl _

end Tape

end ArlibCommunity.Algorithms.CV18
