import TvDomainReduction.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Rand
import Arlib.Computation.Std

/-!
# `#programSeal` — pricing a line by hand

`Charged.op o a` is arlib's escape hatch — one operation of the currency,
returning a value the algorithm computed for itself — and a program may not call
it inline.  Standard operations come from arlib; project-local operations come
from `Model/Operations.lean`.

The cheat below is exactly what the algorithm used to do, and it is the shape to
watch for: the charge says "one coin" and the argument is an `O(level)` scan of a
bare bit block, read at a level nobody paid for.  The seal cannot see that the
argument is expensive — nothing can — so it forbids the escape hatch directly in
`Program.lean`.  The honest fix for a line that genuinely needs one is to expose
the primitive in the operation model.

The original wrote this against the development's own `BitBlock` and
`acceptsAt`, which is the shape the algorithm actually had.  Here it is a bare
function on `Nat`, so that the breach library builds with nothing but arlib and
can be a default target from the first commit of a project.  The property under
test is unchanged: the charge says one coin, and the seal cannot see what the
argument cost.

See `Breach/Exchange.lean` for why each cheat gets its own module and why it is
planted in the canonical namespace.
-/

open Arlib.Computation

namespace TvDomainReduction.Program

def cheatHandPriced (level : Nat) (bits : Nat → Bool) : Charged StdOp Cell Bool :=
  Charged.op (StdOp.rand .accept) (bits level)

end TvDomainReduction.Program

/--
error: Seal breach in TvDomainReduction.Program: [(TvDomainReduction.Program.cheatHandPriced, Arlib.Computation.Charged.op)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal TvDomainReduction.Program
