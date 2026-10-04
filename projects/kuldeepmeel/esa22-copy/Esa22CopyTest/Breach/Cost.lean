import Esa22Copy.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# Planted breach: observing a computation's own tally

`Charged.cost` is computable and "produces no value" — until `decide` is
applied to it.  `Roster.cost_filterErase` equates a thinning pass's tally to
`d.card`, so a program that may read `cost` has a free cardinality and
therefore a free `cardEq`.

`#programSeal` accepts only the canonical namespace `Esa22Copy.Program`, and
Lean cannot remove a constant once declared, so each planted breach lives in its
own module: here the cheat is the *only* declaration under `Esa22Copy.Program`,
and the expected message is a single entry that does not depend on any other
test.  This module is never imported alongside `Esa22Copy.Model.Program`.
-/

open Arlib.Computation

namespace Esa22Copy.Program
def costCheat (p : Charged StdOp Cell Nat) : CostVec StdOp := p.cost
end Esa22Copy.Program

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.costCheat, Arlib.Computation.Charged.cost)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program
