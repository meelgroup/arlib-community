import Esa22Copy.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# Planted breach: silencing the compiler

Writing `noncomputable def` turns off the half of the seal the compiler
provides.  Nothing else about this declaration is wrong, which is the point: the
marker alone is the breach.

`#programSeal` accepts only the canonical namespace `Esa22Copy.Program`, and
Lean cannot remove a constant once declared, so each planted breach lives in its
own module: here the cheat is the *only* declaration under `Esa22Copy.Program`,
and the expected message is a single entry that does not depend on any other
test.  This module is never imported alongside `Esa22Copy.Model.Program`.
-/

open Arlib.Computation

namespace Esa22Copy.Program
noncomputable def noncomputableCheat : Real := 0
end Esa22Copy.Program

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.noncomputableCheat, noncomputableProgram)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program
