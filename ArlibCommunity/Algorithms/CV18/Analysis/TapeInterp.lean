/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.TapeProgram

/-!
# The computation of a tape program, on a tape

`interp_run_val`: running `interp p` from the oracle `Oracle.ofTape member t` with
`budget` calls allowed gives the result, the calls left and the tape left of
`execB member p budget t`.  `interp_run_queryCount`: its tally counts exactly the calls
made, `budget` minus the calls left.
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.CV18

open ArlibCommunity.Algorithms.CV18.Model.Operations
open Arlib.Computation

namespace Program

variable {n : ℕ} {α β : Type}

/-- A computation of `M n`, run from the state `s`. -/
abbrev runFrom (X : M n α) (s : ℕ × Oracle n) : Prog (Option α × (ℕ × Oracle n)) :=
  X.run.run s

theorem runFrom_bind (X : M n α) (F : α → M n β) (s : ℕ × Oracle n) :
    runFrom (X >>= F) s =
      runFrom X s >>= fun r =>
        match r.1 with
        | none => Pure.pure (none, r.2)
        | some a => runFrom (F a) r.2 := by
  simp only [runFrom, OptionT.run_bind, Option.elimM, StateT.run_bind]
  congr 1
  funext r
  rcases r with ⟨_ | a, s'⟩ <;> rfl

theorem runFrom_pure (a : α) (s : ℕ × Oracle n) :
    runFrom (Pure.pure a : M n α) s = Pure.pure (some a, s) := rfl

theorem runFrom_isMember_zero (x : AmbientSpace n) (o : Oracle n) :
    runFrom (isMember x) (0, o) = Pure.pure (none, (0, o)) := rfl

theorem val_isMember_succ (member : AmbientSpace n → Bool) (t : Tape n)
    (x : AmbientSpace n) (b : ℕ) :
    (runFrom (isMember x) (b + 1, Oracle.ofTape member t)).val =
      (some (member x), (b, Oracle.ofTape member t)) := rfl

theorem cost_isMember_succ (member : AmbientSpace n → Bool) (t : Tape n)
    (x : AmbientSpace n) (b : ℕ) :
    (runFrom (isMember x) (b + 1, Oracle.ofTape member t)).cost = CostVec.one Op.query := by
  funext o; cases o <;> rfl

theorem val_ballPoint (member : AmbientSpace n → Bool) (t : Tape n) (b : ℕ) :
    (runFrom ballPoint (b, Oracle.ofTape member t)).val =
      (some (t 0).1, (b, Oracle.ofTape member t.tail)) := rfl

theorem cost_ballPoint (member : AmbientSpace n → Bool) (t : Tape n) (b : ℕ) :
    (runFrom ballPoint (b, Oracle.ofTape member t)).cost = CostVec.one Op.draw := by
  funext o; cases o <;> rfl

theorem val_gaussianVector (member : AmbientSpace n → Bool) (t : Tape n) (b : ℕ) :
    (runFrom gaussianVector (b, Oracle.ofTape member t)).val =
      (some (t 0).2.1, (b, Oracle.ofTape member t.tail)) := rfl

theorem cost_gaussianVector (member : AmbientSpace n → Bool) (t : Tape n) (b : ℕ) :
    (runFrom gaussianVector (b, Oracle.ofTape member t)).cost = CostVec.one Op.draw := by
  funext o; cases o <;> rfl

theorem val_unitNumber (member : AmbientSpace n → Bool) (t : Tape n) (b : ℕ) :
    (runFrom unitNumber (b, Oracle.ofTape member t)).val =
      (some (t 0).2.2, (b, Oracle.ofTape member t.tail)) := rfl

theorem cost_unitNumber (member : AmbientSpace n → Bool) (t : Tape n) (b : ℕ) :
    (runFrom unitNumber (b, Oracle.ofTape member t)).cost = CostVec.one Op.draw := by
  funext o; cases o <;> rfl

end Program

namespace TapeProgram

variable {n : ℕ} {α : Type}

open Program in
/-- **The computation of a tape program, on a tape**: result, calls left and tape left
are those of `execB`. -/
theorem interp_run_val (member : AmbientSpace n → Bool) (p : TapeProgram n α) (b : ℕ)
    (t : Tape n) :
    (runFrom (interp p) (b, Oracle.ofTape member t)).val =
      ((execB member p b t).1,
        ((execB member p b t).2.1, Oracle.ofTape member (execB member p b t).2.2)) := by
  induction p generalizing b t with
  | pure a => rfl
  | query x k ih =>
      cases b with
      | zero => rfl
      | succ b =>
          rw [interp, runFrom_bind, Charged.val_bind, val_isMember_succ]
          exact ih _ b t
  | ball k ih =>
      rw [interp, runFrom_bind, Charged.val_bind, val_ballPoint]
      exact ih _ b _
  | gaussian k ih =>
      rw [interp, runFrom_bind, Charged.val_bind, val_gaussianVector]
      exact ih _ b _
  | unit k ih =>
      rw [interp, runFrom_bind, Charged.val_bind, val_unitNumber]
      exact ih _ b _

open Program in
/-- **The query tally of a tape program, on a tape**: one per membership call made, which
is the budget it started with minus the calls left. -/
theorem interp_run_queryCount (member : AmbientSpace n → Bool) (p : TapeProgram n α)
    (b : ℕ) (t : Tape n) :
    queryCount (runFrom (interp p) (b, Oracle.ofTape member t)).cost +
      (execB member p b t).2.1 = b := by
  induction p generalizing b t with
  | pure a => exact Nat.zero_add b
  | query x k ih =>
      cases b with
      | zero => rfl
      | succ b =>
          have h := ih (member x) b t
          rw [interp, runFrom_bind, Charged.cost_bind, cost_isMember_succ, val_isMember_succ]
          change (CostVec.one Op.query + _) Op.query + _ = b + 1
          simp only [Pi.add_apply, CostVec.one, ite_true]
          change 1 + queryCount _ + _ = b + 1
          exact (by omega : ∀ a c : ℕ, a + c = b → 1 + a + c = b + 1) _ _ h
  | ball k ih =>
      have h := ih (t 0).1 b t.tail
      rw [interp, runFrom_bind, Charged.cost_bind, cost_ballPoint, val_ballPoint]
      change (CostVec.one Op.draw + _) Op.query + _ = b
      simp only [Pi.add_apply, CostVec.one, reduceCtorEq, ite_false, zero_add]
      exact h
  | gaussian k ih =>
      have h := ih (t 0).2.1 b t.tail
      rw [interp, runFrom_bind, Charged.cost_bind, cost_gaussianVector, val_gaussianVector]
      change (CostVec.one Op.draw + _) Op.query + _ = b
      simp only [Pi.add_apply, CostVec.one, reduceCtorEq, ite_false, zero_add]
      exact h
  | unit k ih =>
      have h := ih (t 0).2.2 b t.tail
      rw [interp, runFrom_bind, Charged.cost_bind, cost_unitNumber, val_unitNumber]
      change (CostVec.one Op.draw + _) Op.query + _ = b
      simp only [Pi.add_apply, CostVec.one, reduceCtorEq, ite_false, zero_add]
      exact h

end TapeProgram

end ArlibCommunity.Algorithms.CV18
