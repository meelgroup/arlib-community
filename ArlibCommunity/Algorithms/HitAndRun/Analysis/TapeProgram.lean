/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Model.Run

/-!
# Tape programs: the sampler as a tree

`Program.sampler` (`Model/Program.lean`) is a function of the sealed oracle, and a
function cannot be inducted on.  A `TapeProgram` is the same kind of computation as a
tree: a membership call (`query`), a read of the tape (`gaussian`, `unit`), or a result
(`pure`).  `Analysis/TapeAlgorithm.lean` writes the sampler as tape programs and proves
that interpreting them (`interp`) gives `Program`'s procedures.

A tape program has three readings:

* `interp` — the computation of `Model/Program.lean` it stands for;
* `exec member p t` — what it does on the tape `t` when membership is answered by
  `member`: its result and the tape left;
* `law member p` — its output law when each random number is drawn from its law as it is
  read.

`interp_run_val` connects the first two; `Analysis/TapeLaw.lean` the last two.
-/

set_option autoImplicit false

open MeasureTheory

namespace ArlibCommunity.Algorithms.HitAndRun

open ArlibCommunity.Algorithms.HitAndRun.Model.Operations
open Arlib.Computation

/-- A program as a tree: a membership call, a read of one component of the next round of
the tape, or a result. -/
inductive TapeProgram (n : ℕ) (α : Type) : Type where
  | pure (result : α)
  | query (point : State n) (next : Bool → TapeProgram n α)
  | gaussian (next : State n → TapeProgram n α)
  | unit (next : ℝ → TapeProgram n α)

namespace TapeProgram

variable {n : ℕ} {α β γ : Type}

/-- Sequential composition. -/
def bind : TapeProgram n α → (α → TapeProgram n β) → TapeProgram n β
  | .pure a, f => f a
  | .query x k, f => .query x fun b => (k b).bind f
  | .gaussian k, f => .gaussian fun g => (k g).bind f
  | .unit k, f => .unit fun v => (k v).bind f

instance : Monad (TapeProgram n) where
  pure := .pure
  bind := bind

@[simp] theorem bind_eq (p : TapeProgram n α) (f : α → TapeProgram n β) :
    p >>= f = p.bind f := rfl

@[simp] theorem pure_eq (a : α) : (Pure.pure a : TapeProgram n α) = .pure a := rfl

theorem bind_assoc (p : TapeProgram n α) (f : α → TapeProgram n β) (g : β → TapeProgram n γ) :
    (p.bind f).bind g = p.bind fun a => (f a).bind g := by
  induction p with
  | pure a => rfl
  | query x k ih => simp only [bind, ih]
  | gaussian k ih => simp only [bind, ih]
  | unit k ih => simp only [bind, ih]

theorem bind_pure (p : TapeProgram n α) : p.bind TapeProgram.pure = p := by
  induction p with
  | pure a => rfl
  | query x k ih => simp only [bind, ih]
  | gaussian k ih => simp only [bind, ih]
  | unit k ih => simp only [bind, ih]

instance : LawfulMonad (TapeProgram n) := LawfulMonad.mk'
  (id_map := fun p => bind_pure p)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun p f g => bind_assoc p f g)

/-- One membership call. -/
def isMember (x : State n) : TapeProgram n Bool := .query x .pure

/-- A standard Gaussian vector. -/
def gaussianVector : TapeProgram n (State n) := .gaussian .pure

/-- A uniform number in `[0, 1]`. -/
def unitNumber : TapeProgram n ℝ := .unit .pure

/-! ## The computation a tape program stands for -/

/-- **The computation of `Model/Program.lean` a tape program stands for.** -/
noncomputable def interp : TapeProgram n α → Program.M n α
  | .pure a => Pure.pure a
  | .query x k => Program.isMember x >>= fun b => interp (k b)
  | .gaussian k => Program.gaussianVector >>= fun g => interp (k g)
  | .unit k => Program.unitNumber >>= fun v => interp (k v)

theorem interp_bind (p : TapeProgram n α) (f : α → TapeProgram n β) :
    interp (p.bind f) = interp p >>= fun a => interp (f a) := by
  induction p with
  | pure a => simp only [bind, interp, LawfulMonad.pure_bind]
  | query x k ih => simp only [bind, interp, ih, LawfulMonad.bind_assoc]
  | gaussian k ih => simp only [bind, interp, ih, LawfulMonad.bind_assoc]
  | unit k ih => simp only [bind, interp, ih, LawfulMonad.bind_assoc]

@[simp] theorem interp_bind' (p : TapeProgram n α) (f : α → TapeProgram n β) :
    interp (p >>= f) = interp p >>= fun a => interp (f a) := interp_bind p f

@[simp] theorem interp_pure' (a : α) : interp (Pure.pure a : TapeProgram n α) = Pure.pure a :=
  rfl

@[simp] theorem interp_isMember (x : State n) : interp (isMember x) = Program.isMember x := by
  simp only [isMember, interp]
  exact _root_.bind_pure _

@[simp] theorem interp_gaussianVector :
    interp (gaussianVector (n := n)) = Program.gaussianVector := by
  simp only [gaussianVector, interp]
  exact _root_.bind_pure _

@[simp] theorem interp_unitNumber : interp (unitNumber (n := n)) = Program.unitNumber := by
  simp only [unitNumber, interp]
  exact _root_.bind_pure _

theorem interp_ite (c : Prop) [Decidable c] (a b : TapeProgram n α) :
    interp (if c then a else b) = if c then interp a else interp b := by
  split <;> rfl

/-! ## The run on a tape -/

/-- **What a tape program does on the tape `t`**, membership answered by `member`: the
result and the tape left. -/
def exec (member : State n → Bool) : TapeProgram n α → Tape n → α × Tape n
  | .pure a, t => (a, t)
  | .query x k, t => exec member (k (member x)) t
  | .gaussian k, t => exec member (k (t 0).1) t.tail
  | .unit k, t => exec member (k (t 0).2) t.tail

theorem exec_bind (member : State n → Bool) (p : TapeProgram n α)
    (f : α → TapeProgram n β) (t : Tape n) :
    exec member (p.bind f) t =
      exec member (f (exec member p t).1) (exec member p t).2 := by
  induction p generalizing t with
  | pure a => rfl
  | query x k ih => exact ih _ t
  | gaussian k ih => exact ih _ _
  | unit k ih => exact ih _ _

/-- **The computation of a tape program, on a tape**: result and tape left are those of
`exec`. -/
theorem interp_run_val (member : State n → Bool) (p : TapeProgram n α) (t : Tape n) :
    ((interp p).run (Oracle.ofTape member t)).val =
      ((exec member p t).1, Oracle.ofTape member (exec member p t).2) := by
  induction p generalizing t with
  | pure a => rfl
  | query x k ih => exact ih _ t
  | gaussian k ih => exact ih _ _
  | unit k ih => exact ih _ _

/-! ## The law -/

/-- **The output law of a tape program** when each random number is drawn from its law as
it is read: a Gaussian vector from `standardGaussian n`, a number from `uniformUnit`. -/
noncomputable def law [MeasurableSpace α] (member : State n → Bool) :
    TapeProgram n α → Measure α
  | .pure a => Measure.dirac a
  | .query x k => law member (k (member x))
  | .gaussian k => (standardGaussian n).bind fun g => law member (k g)
  | .unit k => uniformUnit.bind fun v => law member (k v)

end TapeProgram

end ArlibCommunity.Algorithms.HitAndRun
