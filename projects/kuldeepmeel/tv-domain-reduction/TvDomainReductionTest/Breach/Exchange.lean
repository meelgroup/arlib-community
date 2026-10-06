import TvDomainReduction.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Std

/-!
# `#programSeal` — laundering a tally through a change of currency

`exchange` is computable and takes a `Charged` to a `Charged`, so nothing the
compiler checks stands in the way; at a rate of zero it re-prices any computation
at nothing.

One breach per module, and the cheat is planted in the **canonical** program
namespace `TvDomainReduction.Program`: `#programSeal` scans that namespace and no
other, so a cheat planted anywhere else is not a thing the seal is asked about.
The module boundary is what keeps each expected message a single entry and keeps
the tests independent of the order they run in — a second cheat in this file
would appear in the first test's message too.  Nothing of the real algorithm is
in scope here (this module does not import `Model/Program.lean`), so the one
declaration below is the whole of what the seal sees.

The cheats are named apart (`cheatExchange`, `cheatCost`, …) only because
`TvDomainReductionTest.lean` imports all eight modules into one environment, and
two declarations cannot share a name there.  Nothing in the test depends on the
name.
-/

open Arlib.Computation

namespace TvDomainReduction.Program

def cheatExchange (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat :=
  Charged.exchange (fun _ => (0 : CostVec StdOp)) p

end TvDomainReduction.Program

/--
error: Seal breach in TvDomainReduction.Program: [(TvDomainReduction.Program.cheatExchange, Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal TvDomainReduction.Program
