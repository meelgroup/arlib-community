import Esa22Copy.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# Planted breach: pricing a line by hand

`Charged.op o a` is arlib's escape hatch — one operation of the currency,
returning a value the algorithm computed for itself — and a program may not call
it inline.  Standard operations come from arlib; project-local operations come
from `Model/Operations.lean`.  The charge below says "one coin" and the
argument is a read of a bare bit block at a level nobody paid for.  The seal
cannot see that the argument is expensive — nothing can — so it forbids the
escape hatch directly.  (Written against a bare `Nat → Bool` so that the breach
builds with nothing but arlib; the property under test is unchanged.)

`#programSeal` accepts only the canonical namespace `Esa22Copy.Program`, and
Lean cannot remove a constant once declared, so each planted breach lives in its
own module: here the cheat is the *only* declaration under `Esa22Copy.Program`,
and the expected message is a single entry that does not depend on any other
test.  This module is never imported alongside `Esa22Copy.Model.Program`.
-/

open Arlib.Computation

namespace Esa22Copy.Program
def handPricedCheat (level : Nat) (bits : Nat → Bool) : Charged StdOp Cell Bool :=
  Charged.op (StdOp.rand .accept) (bits level)
end Esa22Copy.Program

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.handPricedCheat, Arlib.Computation.Charged.op)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program
