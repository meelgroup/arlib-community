/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.ModelSupport

/-!
# The pseudocode is the analysed program

`cv18Program` (`Model/Pseudocode.lean`) is written in `do` notation for
readability.  The proof of Theorem 1.1 was developed against the same
algorithm written with the program constructors
(`Analysis/ScheduledProgram.lean`).  This file proves the two are equal
(`cv18Program_eq`), subroutine by subroutine, and that the syntax-level query
certificate `QueryBound` bounds the cost model `queryCost`.
-/

namespace ArlibCommunity.Algorithms.CV18

variable (q : VolumeParams)

section Bridge
variable {n : ℕ} {α β γ : Type}

@[simp] theorem bind_eq (p : MembershipOracleProgram n α)
    (f : α → MembershipOracleProgram n β) : p >>= f = p.bind f := rfl

@[simp] theorem pure_eq (a : α) : (pure a : MembershipOracleProgram n α) = .pure a := rfl

@[simp] theorem pure_bind' (a : α) (f : α → MembershipOracleProgram n β) :
    (MembershipOracleProgram.pure a).bind f = f a := rfl

theorem bind_assoc' (p : MembershipOracleProgram n α)
    (f : α → MembershipOracleProgram n β) (g : β → MembershipOracleProgram n γ) :
    (p.bind f).bind g = p.bind fun x => (f x).bind g := by
  induction p with
  | pure a => rfl
  | query x next ih => simp only [MembershipOracleProgram.bind, ih]
  | randomNat law next ih => simp only [MembershipOracleProgram.bind, ih]
  | randomPoint law h next ih => simp only [MembershipOracleProgram.bind, ih]
  | randomReal law h next ih => simp only [MembershipOracleProgram.bind, ih]

end Bridge

theorem ballWalkStep_eq (sigma2 : ℝ) (x : AmbientSpace q.n) :
    ballWalkStep q sigma2 x = scheduledAccuracyMetropolisMarkedBallStep q sigma2 x := rfl

theorem rejectionAttempt_eq (sigma2 : ℝ) (x : AmbientSpace q.n) :
    rejectionAttempt q sigma2 x =
      scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 x := rfl

theorem initialSample_eq : initialSample q = figureOneAbortInitialSample q := rfl

theorem properWalk_eq (sigma2 : ℝ) (stride : ℕ) :
    ∀ (cap steps : ℕ) (x : AmbientSpace q.n),
      cappedScheduledAccuracyProperBlockAux q sigma2 stride cap steps x =
        (properWalk q sigma2 cap steps x).bind
          fun r => .pure (r.map fun y => ((0 : ℝ), y)) := by
  intro cap
  induction cap with
  | zero => intro steps x; simp [cappedScheduledAccuracyProperBlockAux, properWalk]
  | succ cap ih =>
    intro steps x
    cases steps with
    | zero =>
      simp only [cappedScheduledAccuracyProperBlockAux, properWalk, bind_eq, pure_eq,
        scheduledAccuracyZeroObservation, isMember, MembershipOracleProgram.bind]
      rfl
    | succ steps =>
      rw [cappedScheduledAccuracyProperBlockAux, properWalk]
      simp only [bind_eq, bind_assoc', ← ballWalkStep_eq]
      congr 1
      funext r
      obtain ⟨proper, y⟩ := r
      cases proper <;> cases steps <;> simp [ih]


theorem collectSamples_eq (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (cap steps retries : ℕ) :
    ∀ (samplesLeft retriesLeft : ℕ) (total : ℝ) (x : AmbientSpace q.n),
      scheduledBalancedAccuracyRetryCollectAux q sigma2 weight cap steps retries
          retriesLeft samplesLeft total x =
        collectSamples q sigma2 weight cap steps retries retriesLeft samplesLeft total x := by
  intro samplesLeft
  induction samplesLeft with
  | zero =>
    intro retriesLeft total x
    cases retriesLeft <;>
      simp [scheduledBalancedAccuracyRetryCollectAux, collectSamples]
  | succ samplesLeft ihS =>
    intro retriesLeft
    induction retriesLeft with
    | zero =>
      intro total x
      simp [scheduledBalancedAccuracyRetryCollectAux, collectSamples]
    | succ retriesLeft ihR =>
      intro total x
      rw [scheduledBalancedAccuracyRetryCollectAux, collectSamples,
        cappedScheduledAccuracyProperBlock, properWalk_eq]
      simp only [bind_eq, bind_assoc', pure_eq]
      congr 1
      funext r
      cases r with
      | none => rfl
      | some y =>
        simp only [Option.map_some, pure_bind', ← rejectionAttempt_eq]
        congr 1
        funext a
        obtain ⟨accepted, z⟩ := a
        cases accepted
        · simp [ihR]
        · simp [ihS]

theorem coolingPhase_eq (sigma2 tau2 : ℝ) (x : AmbientSpace q.n) :
    coolingPhase q sigma2 tau2 x =
      scheduledBalancedCoolingRatioEstimate figureOneFinalScheduledBalancedParameters
        q sigma2 tau2 x := by
  simp only [coolingPhase, scheduledBalancedCoolingRatioEstimate,
    scheduledBalancedAccuracyRetryCollect, figureOneFinalScheduledBalancedParameters,
    walkSteps, bind_eq, bind_assoc', pure_eq, pure_bind', collectSamples_eq]
  congr 1
  funext r
  rcases r with _ | ⟨total, y⟩ <;> rfl

theorem uniformPhase_eq (sigma2 : ℝ) (x : AmbientSpace q.n) :
    uniformPhase q sigma2 x =
      scheduledBalancedCoolingUniformRatioEstimate figureOneFinalScheduledBalancedParameters
        q sigma2 x := by
  simp only [uniformPhase, scheduledBalancedCoolingUniformRatioEstimate,
    scheduledBalancedCoolingUniformEstimateWithState,
    scheduledBalancedAccuracyRetryCollect, figureOneFinalScheduledBalancedParameters,
    walkSteps, bind_eq, bind_assoc', pure_eq, pure_bind', collectSamples_eq]
  congr 1
  funext r
  rcases r with _ | ⟨total, y⟩ <;> rfl

theorem coolingPhases_eq :
    ∀ (variances : List ℝ) (x : AmbientSpace q.n),
      coolingPhases q variances x =
        coolingProduct (scheduledBalancedAbortCoolingPrimitives
          figureOneFinalScheduledBalancedParameters) q variances x := by
  intro variances
  induction variances with
  | nil => intro x; simp [coolingPhases, coolingProduct]
  | cons sigma2 rest ih =>
    intro x
    cases rest with
    | nil => simp [coolingPhases, coolingProduct]
    | cons tau2 rest =>
      rw [coolingPhases, coolingProduct]
      simp only [bind_eq, pure_eq, scheduledBalancedAbortCoolingPrimitives,
        coolingPhase_eq]
      congr 1
      funext r
      rcases r with _ | ⟨W, y⟩
      · rfl
      · simp only [ih]
        congr 1
        funext t
        rcases t with _ | ⟨product, z⟩ <;> rfl

theorem figureOneRun_eq : figureOneRun q = figureOneFinalScheduledAbortBaseProgram q := by
  simp only [figureOneRun, figureOneFinalScheduledAbortBaseProgram, baseVolumeCoolingOn,
    bind_eq, pure_eq, ← initialSample_eq, scheduledBalancedAbortCoolingPrimitives]
  congr 1
  funext r
  rcases r with _ | x₀
  · rfl
  · simp only [coolingPhases_eq, scheduledBalancedAbortCoolingPrimitives]
    congr 1
    funext t
    rcases t with _ | ⟨product, x⟩
    · rfl
    · simp only [← uniformPhase_eq]
      congr 1
      funext u
      rcases u with _ | U <;> rfl

theorem cappedRun_eq : cappedRun q = figureOneFinalScheduledCappedValueProgram q := by
  simp only [cappedRun, figureOneFinalScheduledCappedValueProgram, figureOneRun_eq]
  rfl

theorem repeatIndependently_eq {n : ℕ} (run : MembershipOracleProgram n ℝ) :
    ∀ m, repeatIndependently run m = repeatOracleProgram run m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => simp only [repeatIndependently, repeatOracleProgram, bind_eq, pure_eq, ih]

theorem cv18Program_eq :
    cv18Program = amplifyOracleProgram figureOneFinalScheduledCappedValueProgram := by
  funext q
  simp only [cv18Program, amplifyOracleProgram, bind_eq, pure_eq,
    repeatIndependently_eq, cappedRun_eq]

theorem MembershipOracleProgram.QueryBound.queryCost_le {n : ℕ} {α : Type} {p : MembershipOracleProgram n α}
    {budget : ℕ} (h : p.QueryBound budget) : p.queryCost ≤ budget := by
  induction h with
  | pure => simp [MembershipOracleProgram.queryCost]
  | query point next budget hnext ih =>
    simp only [MembershipOracleProgram.queryCost, Nat.cast_add, Nat.cast_one]
    rw [add_comm (budget : ℕ∞)]
    exact add_le_add le_rfl (iSup_le ih)
  | randomNat law next budget hnext ih => exact iSup_le ih
  | randomPoint law hprob next budget hnext ih => exact iSup_le ih
  | randomReal law hprob next budget hnext ih => exact iSup_le ih

#print axioms cv18Program_eq

end ArlibCommunity.Algorithms.CV18
