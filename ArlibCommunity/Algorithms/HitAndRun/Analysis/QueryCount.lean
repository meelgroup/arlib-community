/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.Run

/-!
# The membership calls of the sampler

On every oracle, one step of `Program.walk` makes at most
`2 · bisectionSteps + rejectionTries` membership calls (`step_queryCount_le`), so the
sampler makes at most `steps · (2 · bisectionSteps + rejectionTries)`
(`execution_queryCount_le`).  The bound is read off the program's own tally.
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Algorithms.HitAndRun.Model.Operations
open Arlib.Computation

namespace Program

variable {n : ℕ} {α β : Type}

/-- The calls a computation of `M n` makes from the oracle `o`. -/
def calls (X : M n α) (o : Oracle n) : ℕ := queryCount (X.run o).cost

theorem calls_bind (X : M n α) (F : α → M n β) (o : Oracle n) :
    calls (X >>= F) o = calls X o + calls (F (X.run o).val.1) (X.run o).val.2 := rfl

theorem calls_pure (a : α) (o : Oracle n) : calls (Pure.pure a : M n α) o = 0 := rfl

theorem calls_isMember (x : State n) (o : Oracle n) : calls (isMember x) o = 1 := rfl

theorem calls_gaussianVector (o : Oracle n) : calls (gaussianVector (n := n)) o = 0 := rfl

theorem calls_unitNumber (o : Oracle n) : calls (unitNumber (n := n)) o = 0 := rfl

/-- `X` makes at most `k` calls from every oracle. -/
def CallsLe (X : M n α) (k : ℕ) : Prop := ∀ o, calls X o ≤ k

theorem CallsLe.mono {X : M n α} {k k' : ℕ} (h : CallsLe X k) (hk : k ≤ k') : CallsLe X k' :=
  fun o => (h o).trans hk

theorem CallsLe.pure (a : α) : CallsLe (Pure.pure a : M n α) 0 := fun _ => le_rfl

theorem CallsLe.bind {X : M n α} {F : α → M n β} {a b : ℕ} (hX : CallsLe X a)
    (hF : ∀ x, CallsLe (F x) b) : CallsLe (X >>= F) (a + b) := fun o => by
  rw [calls_bind]
  exact add_le_add (hX o) (hF _ _)

theorem CallsLe.ite (c : Prop) [Decidable c] {X Y : M n α} {k : ℕ} (hX : CallsLe X k)
    (hY : CallsLe Y k) : CallsLe (if c then X else Y) k := by
  split
  · exact hX
  · exact hY

theorem callsLe_isMember (x : State n) : CallsLe (isMember x) 1 := fun _ => le_rfl

theorem callsLe_gaussianVector : CallsLe (gaussianVector (n := n)) 0 := fun _ => le_rfl

theorem callsLe_unitNumber : CallsLe (unitNumber (n := n)) 0 := fun _ => le_rfl

theorem callsLe_bisect (x θ : State n) :
    ∀ (k : ℕ) (inner outer : ℝ), CallsLe (bisect x θ k inner outer) k
  | 0, _, _ => CallsLe.pure _
  | k + 1, inner, outer => by
      rw [bisect, Nat.add_comm]
      exact (callsLe_isMember _).bind fun _ =>
        CallsLe.ite _ (callsLe_bisect x θ k _ _) (callsLe_bisect x θ k _ _)

theorem callsLe_chordPoint (x θ : State n) (lo hi : ℝ) :
    ∀ r : ℕ, CallsLe (chordPoint x θ lo hi r) r
  | 0 => CallsLe.pure _
  | r + 1 => by
      rw [chordPoint]
      refine (callsLe_unitNumber.bind fun _ => (callsLe_isMember _).bind fun _ =>
        CallsLe.ite _ ((CallsLe.pure _).mono (Nat.zero_le r))
          (callsLe_chordPoint x θ lo hi r)).mono ?_
      omega

/-- **One step makes at most `2 · bisectionSteps + rejectionTries` calls.** -/
theorem callsLe_step (w : WalkParams) (x : State n) :
    CallsLe (step w x) (2 * w.bisectionSteps + w.rejectionTries) := by
  rw [step]
  refine (callsLe_unitNumber.bind fun _ => CallsLe.ite _
    ((CallsLe.pure _).mono (Nat.zero_le _))
    (callsLe_gaussianVector.bind fun _ => (callsLe_bisect _ _ _ _ _).bind fun _ =>
      (callsLe_bisect _ _ _ _ _).bind fun _ => callsLe_chordPoint _ _ _ _ _)).mono ?_
  omega

theorem callsLe_walk (w : WalkParams) :
    ∀ (m : ℕ) (x : State n), CallsLe (walk w m x) (m * (2 * w.bisectionSteps + w.rejectionTries))
  | 0, _ => fun _ => Nat.zero_le _
  | m + 1, x => by
      rw [walk]
      refine ((callsLe_step w x).bind fun y => callsLe_walk w m y).mono ?_
      rw [add_mul, one_mul, add_comm]

end Program

/-- **The query bound**: on every tape, and whatever answers membership, the sampler makes
at most `steps · (2 · bisectionSteps + rejectionTries)` membership calls. -/
theorem execution_queryCount_le {n : ℕ} (w : WalkParams) (member : State n → Bool)
    (x₀ : State n) (t : Tape n) :
    queryCount (Charged.cost (execution w member x₀ t)) ≤
      w.steps * (2 * w.bisectionSteps + w.rejectionTries) := by
  have h := Program.callsLe_walk w w.steps x₀ (Oracle.ofTape member t)
  show queryCount ((Program.walk w w.steps x₀).run (Oracle.ofTape member t)).cost + 0 ≤ _
  simpa [Program.calls] using h

end ArlibCommunity.Algorithms.HitAndRun
