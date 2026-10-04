import Esa22Copy.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# Planted breach: projecting a dictionary's contents through the eliminator

`casesOn` is generated public even though the constructor is private, and it is
compiled, so this is the one route the compiler genuinely leaves open.

`#programSeal` accepts only the canonical namespace `Esa22Copy.Program`, and
Lean cannot remove a constant once declared, so each planted breach lives in its
own module: here the cheat is the *only* declaration under `Esa22Copy.Program`,
and the expected message is a single entry that does not depend on any other
test.  This module is never imported alongside `Esa22Copy.Model.Program`.
-/

open Arlib.Computation

namespace Esa22Copy.Program
def casesOnCheat (d : Roster Nat) : Nat :=
  Roster.casesOn (motive := fun _ => Nat) d (fun elems _ => elems.length)
end Esa22Copy.Program

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.casesOnCheat, Arlib.Computation.Roster.casesOn)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program
