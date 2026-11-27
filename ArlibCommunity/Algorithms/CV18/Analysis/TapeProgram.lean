/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Run
import ArlibCommunity.Algorithms.CV18.Analysis.OracleProgram

/-!
# Tape programs: the program as a tree

`Program.estimator` (`Model/Program.lean`) is a function of the sealed oracle, and a
function cannot be inducted on.  A `TapeProgram` is the same kind of computation as a
tree: a membership call (`query`), a read of the tape (`ball`, `gaussian`, `unit`), or a
result (`pure`).  `Analysis/TapeBridge.lean` writes the algorithm as tape programs and
proves that interpreting them (`interp`) gives `Program.estimator`'s procedures.

A tape program has three readings:

* `interp` — the computation of `Model/Program.lean` it stands for;
* `execB member p budget t` — what it does on the tape `t` when membership is answered by
  `member` and at most `budget` calls are allowed: its result (`none` if it ran out of
  calls), the calls left, and the tape left (`exec` is the same with no limit);
* `toOP` — the membership-oracle program tree of `Analysis/OracleProgram.lean` that draws
  each random number from its law.

`interp_run` connects the first two; `Analysis/TapeLaw.lean` connects the last two.
-/

set_option autoImplicit false

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

open ArlibCommunity.Algorithms.CV18.Model.Operations
open Arlib.Computation

/-- A program as a tree: a membership call, a read of one component of the next round of
the tape, or a result. -/
inductive TapeProgram (n : ℕ) (α : Type) : Type where
  | pure (result : α)
  | query (point : AmbientSpace n) (next : Bool → TapeProgram n α)
  | ball (next : AmbientSpace n → TapeProgram n α)
  | gaussian (next : AmbientSpace n → TapeProgram n α)
  | unit (next : ℝ → TapeProgram n α)

namespace TapeProgram

variable {n : ℕ} {α β γ : Type}

/-- Sequential composition. -/
def bind : TapeProgram n α → (α → TapeProgram n β) → TapeProgram n β
  | .pure a, f => f a
  | .query x k, f => .query x fun b => (k b).bind f
  | .ball k, f => .ball fun u => (k u).bind f
  | .gaussian k, f => .gaussian fun g => (k g).bind f
  | .unit k, f => .unit fun v => (k v).bind f

instance : Monad (TapeProgram n) where
  pure := .pure
  bind := bind

@[simp] theorem bind_eq (p : TapeProgram n α) (f : α → TapeProgram n β) :
    p >>= f = p.bind f := rfl

@[simp] theorem pure_eq (a : α) : (Pure.pure a : TapeProgram n α) = .pure a := rfl

@[simp] theorem pure_bind (a : α) (f : α → TapeProgram n β) : (TapeProgram.pure a).bind f = f a :=
  rfl

theorem bind_assoc (p : TapeProgram n α) (f : α → TapeProgram n β) (g : β → TapeProgram n γ) :
    (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  induction p with
  | pure a => rfl
  | query x k ih => simp only [bind, ih]
  | ball k ih => simp only [bind, ih]
  | gaussian k ih => simp only [bind, ih]
  | unit k ih => simp only [bind, ih]

theorem bind_pure (p : TapeProgram n α) : p.bind TapeProgram.pure = p := by
  induction p with
  | pure a => rfl
  | query x k ih => simp only [bind, ih]
  | ball k ih => simp only [bind, ih]
  | gaussian k ih => simp only [bind, ih]
  | unit k ih => simp only [bind, ih]

instance : LawfulMonad (TapeProgram n) := LawfulMonad.mk'
  (id_map := fun p => bind_pure p)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun p f g => bind_assoc p f g)

/-- One membership call. -/
def isMember (x : AmbientSpace n) : TapeProgram n Bool := .query x .pure

/-- A uniform point of the closed unit ball. -/
def ballPoint : TapeProgram n (AmbientSpace n) := .ball .pure

/-- A standard Gaussian vector. -/
def gaussianVector : TapeProgram n (AmbientSpace n) := .gaussian .pure

/-- A uniform number in `[0, 1]`. -/
def unitNumber : TapeProgram n ℝ := .unit .pure

/-! ## The computation a tape program stands for -/

/-- **The computation of `Model/Program.lean` a tape program stands for**: each node is
the corresponding primitive of `Program`. -/
noncomputable def interp : TapeProgram n α → Program.M n α
  | .pure a => Pure.pure a
  | .query x k => Program.isMember x >>= fun b => interp (k b)
  | .ball k => Program.ballPoint >>= fun u => interp (k u)
  | .gaussian k => Program.gaussianVector >>= fun g => interp (k g)
  | .unit k => Program.unitNumber >>= fun v => interp (k v)

theorem interp_bind (p : TapeProgram n α) (f : α → TapeProgram n β) :
    interp (p.bind f) = interp p >>= fun a => interp (f a) := by
  induction p with
  | pure a => simp only [bind, interp, LawfulMonad.pure_bind]
  | query x k ih => simp only [bind, interp, ih, LawfulMonad.bind_assoc]
  | ball k ih => simp only [bind, interp, ih, LawfulMonad.bind_assoc]
  | gaussian k ih => simp only [bind, interp, ih, LawfulMonad.bind_assoc]
  | unit k ih => simp only [bind, interp, ih, LawfulMonad.bind_assoc]

@[simp] theorem interp_bind' (p : TapeProgram n α) (f : α → TapeProgram n β) :
    interp (p >>= f) = interp p >>= fun a => interp (f a) := interp_bind p f

@[simp] theorem interp_pure (a : α) : interp (TapeProgram.pure (n := n) a) = Pure.pure a := rfl

@[simp] theorem interp_pure' (a : α) : interp (Pure.pure a : TapeProgram n α) = Pure.pure a :=
  rfl

@[simp] theorem interp_isMember (x : AmbientSpace n) :
    interp (isMember x) = Program.isMember x := by
  simp only [isMember, interp]
  exact _root_.bind_pure _

@[simp] theorem interp_ballPoint : interp (ballPoint (n := n)) = Program.ballPoint := by
  simp only [ballPoint, interp]
  exact _root_.bind_pure _

@[simp] theorem interp_gaussianVector :
    interp (gaussianVector (n := n)) = Program.gaussianVector := by
  simp only [gaussianVector, interp]
  exact _root_.bind_pure _

@[simp] theorem interp_unitNumber : interp (unitNumber (n := n)) = Program.unitNumber := by
  simp only [unitNumber, interp]
  exact _root_.bind_pure _

/-! ## The run on a tape -/

/-- **What a tape program does on the tape `t`**, with membership answered by `member`
and at most `budget` calls allowed: the result (`none` if it ran out of calls), the
calls left, and the tape left. -/
def execB (member : AmbientSpace n → Bool) : TapeProgram n α → ℕ → Tape n →
    Option α × ℕ × Tape n
  | .pure a, b, t => (some a, b, t)
  | .query _ _, 0, t => (none, 0, t)
  | .query x k, b + 1, t => execB member (k (member x)) b t
  | .ball k, b, t => execB member (k (t 0).1) b t.tail
  | .gaussian k, b, t => execB member (k (t 0).2.1) b t.tail
  | .unit k, b, t => execB member (k (t 0).2.2) b t.tail

/-- **What a tape program does on the tape `t`** with no limit on membership calls: the
result and the tape left. -/
def exec (member : AmbientSpace n → Bool) : TapeProgram n α → Tape n → α × Tape n
  | .pure a, t => (a, t)
  | .query x k, t => exec member (k (member x)) t
  | .ball k, t => exec member (k (t 0).1) t.tail
  | .gaussian k, t => exec member (k (t 0).2.1) t.tail
  | .unit k, t => exec member (k (t 0).2.2) t.tail

theorem execB_bind (member : AmbientSpace n → Bool) (p : TapeProgram n α)
    (f : α → TapeProgram n β) (b : ℕ) (t : Tape n) :
    execB member (p.bind f) b t =
      match execB member p b t with
      | (none, b', t') => (none, b', t')
      | (some a, b', t') => execB member (f a) b' t' := by
  induction p generalizing b t with
  | pure a => rfl
  | query x k ih =>
      cases b with
      | zero => rfl
      | succ b => exact ih _ b t
  | ball k ih => exact ih _ b _
  | gaussian k ih => exact ih _ b _
  | unit k ih => exact ih _ b _

theorem exec_bind (member : AmbientSpace n → Bool) (p : TapeProgram n α)
    (f : α → TapeProgram n β) (t : Tape n) :
    exec member (p.bind f) t =
      exec member (f (exec member p t).1) (exec member p t).2 := by
  induction p generalizing t with
  | pure a => rfl
  | query x k ih => exact ih _ t
  | ball k ih => exact ih _ _
  | gaussian k ih => exact ih _ _
  | unit k ih => exact ih _ _

/-- Run a tape program with a budget of `budget` membership calls.  A call beyond the
budget stops the program with result `none`. -/
def withQueryCap : ℕ → TapeProgram n α → TapeProgram n (Option α)
  | _, .pure a => .pure (some a)
  | 0, .query _ _ => .pure none
  | b + 1, .query x k => .query x fun ans => withQueryCap b (k ans)
  | b, .ball k => .ball fun u => withQueryCap b (k u)
  | b, .gaussian k => .gaussian fun g => withQueryCap b (k g)
  | b, .unit k => .unit fun v => withQueryCap b (k v)

/-- Capping the calls is running with a budget. -/
theorem exec_withQueryCap (member : AmbientSpace n → Bool) (p : TapeProgram n α) (b : ℕ)
    (t : Tape n) :
    exec member (p.withQueryCap b) t =
      ((execB member p b t).1, (execB member p b t).2.2) := by
  induction p generalizing b t with
  | pure a => rfl
  | query x k ih =>
      cases b with
      | zero => rfl
      | succ b => exact ih _ b t
  | ball k ih => exact ih _ b _
  | gaussian k ih => exact ih _ b _
  | unit k ih => exact ih _ b _

/-! ## The membership-oracle program tree -/

/-- **The program tree that draws each random number from its law**: a read of the unit
ball point is a draw from `centeredBall n 1`, of the Gaussian vector a draw from
`standardGaussian n`, of the uniform number a draw from `uniformUnit`. -/
noncomputable def toOP : TapeProgram n α → MembershipOracleProgram n α
  | .pure a => .pure a
  | .query x k => .query x fun b => toOP (k b)
  | .ball k => .randomPoint (centeredBall n 1) inferInstance fun u => toOP (k u)
  | .gaussian k => .randomPoint (standardGaussian n) inferInstance fun g => toOP (k g)
  | .unit k => .randomReal uniformUnit inferInstance fun v => toOP (k v)

theorem toOP_bind (p : TapeProgram n α) (f : α → TapeProgram n β) :
    toOP (p.bind f) = (toOP p).bind fun a => toOP (f a) := by
  induction p with
  | pure a => rfl
  | query x k ih => simp only [bind, toOP, MembershipOracleProgram.bind, ih]
  | ball k ih => simp only [bind, toOP, MembershipOracleProgram.bind, ih]
  | gaussian k ih => simp only [bind, toOP, MembershipOracleProgram.bind, ih]
  | unit k ih => simp only [bind, toOP, MembershipOracleProgram.bind, ih]

theorem toOP_withQueryCap (p : TapeProgram n α) (b : ℕ) :
    toOP (p.withQueryCap b) = (toOP p).withQueryCap b := by
  induction p generalizing b with
  | pure a => cases b <;> rfl
  | query x k ih =>
      cases b with
      | zero => rfl
      | succ b => simp only [withQueryCap, toOP, MembershipOracleProgram.withQueryCap, ih]
  | ball k ih => simp only [withQueryCap, toOP, MembershipOracleProgram.withQueryCap, ih]
  | gaussian k ih => simp only [withQueryCap, toOP, MembershipOracleProgram.withQueryCap, ih]
  | unit k ih => simp only [withQueryCap, toOP, MembershipOracleProgram.withQueryCap, ih]

end TapeProgram

end ArlibCommunity.Algorithms.CV18
