import Esa22Copy.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# Planted breach: the same read, one hop away

`Charged.steps` is deliberately absent from `forbiddenInProgram`: it is
`CostVec.steps C p.cost`, so a blacklist of *direct* mentions would miss it
entirely.  This test is what makes the transitive walk a checked fact rather than
an intention, and it is the one to run first if `reaches` is ever changed.
The message names the intermediary the program actually called, not the
forbidden constant behind it.

`#programSeal` accepts only the canonical namespace `Esa22Copy.Program`, and
Lean cannot remove a constant once declared, so each planted breach lives in its
own module: here the cheat is the *only* declaration under `Esa22Copy.Program`,
and the expected message is a single entry that does not depend on any other
test.  This module is never imported alongside `Esa22Copy.Model.Program`.
-/

open Arlib.Computation

namespace Esa22Copy.Program
def transitiveCheat (p : Charged StdOp Cell Nat) : Nat := Charged.steps (Rate.unit StdOp) p
end Esa22Copy.Program

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.transitiveCheat, Arlib.Computation.Charged.steps)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program
