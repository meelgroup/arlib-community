import Formalization3sum.Meta.CostSeal
import Arlib.Computation.Std
import Arlib.Computation.Roster
import Arlib.Computation.Charged

open Arlib.Computation

namespace Formalization3sum.Program
def cheatCost (p : Charged StdOp Cell Nat) : CostVec StdOp := p.cost
end Formalization3sum.Program

/--
error: Seal breach in Formalization3sum.Program: [(Formalization3sum.Program.cheatCost, Arlib.Computation.Charged.cost)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Formalization3sum.Program
