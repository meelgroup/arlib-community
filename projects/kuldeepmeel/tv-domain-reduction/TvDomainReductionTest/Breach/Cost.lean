import TvDomainReduction.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Std

/-!
# `#programSeal` — observing a computation's own tally

`Charged.cost` is computable and "produces no value" — until `decide` is applied
to it.  `Roster.cost_filterErase` equates a thinning pass's tally to `d.card`, so
a program that may read `cost` has a free cardinality and therefore a free
`cardEq`.

See `Breach/Exchange.lean` for why each cheat gets its own module and why it is
planted in the canonical namespace.
-/

open Arlib.Computation

namespace TvDomainReduction.Program

def cheatCost (p : Charged StdOp Cell Nat) : CostVec StdOp := p.cost

end TvDomainReduction.Program

/--
error: Seal breach in TvDomainReduction.Program: [(TvDomainReduction.Program.cheatCost, Arlib.Computation.Charged.cost)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal TvDomainReduction.Program
