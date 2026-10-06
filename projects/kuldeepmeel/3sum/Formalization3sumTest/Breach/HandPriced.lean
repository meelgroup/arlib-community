import Formalization3sum.Meta.CostSeal
import Arlib.Computation.Std
import Arlib.Computation.Roster
import Arlib.Computation.Charged

open Arlib.Computation

namespace Formalization3sum.Program
-- The original wrote this against the development's own `BitBlock` and
-- `acceptsAt`, which is the shape the algorithm actually had. Here it is a
-- bare function on `Nat`, so that the breach library builds with nothing but
-- arlib and can be a default target from the first commit of a project. The
-- property under test is unchanged: the charge says one coin, and the seal
-- cannot see what the argument cost.
def cheatHandPriced (level : Nat) (bits : Nat → Bool) : Charged StdOp Cell Bool :=
  Charged.op (StdOp.rand .accept) (bits level)
end Formalization3sum.Program

/--
error: Seal breach in Formalization3sum.Program: [(Formalization3sum.Program.cheatHandPriced, Arlib.Computation.Charged.op)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Formalization3sum.Program
