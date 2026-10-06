import TvDomainReduction.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Std

/-!
# `#programSeal` — the same read, one hop away

`Charged.steps` is deliberately absent from `forbiddenInProgram`: it is
`CostVec.steps C p.cost`, so a blacklist of *direct* mentions would miss it
entirely.  This test is what makes the transitive walk a checked fact rather than
an intention, and it is the one to run first if `reaches` is ever changed.

Note which constant the message names — the intermediary the program actually
called, not the forbidden constant behind it.  That is the name whose call site
has to change.

See `Breach/Exchange.lean` for why each cheat gets its own module and why it is
planted in the canonical namespace.
-/

open Arlib.Computation

namespace TvDomainReduction.Program

def cheatTransitive (p : Charged StdOp Cell Nat) : Nat := Charged.steps (Rate.unit StdOp) p

end TvDomainReduction.Program

/--
error: Seal breach in TvDomainReduction.Program: [(TvDomainReduction.Program.cheatTransitive, Arlib.Computation.Charged.steps)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal TvDomainReduction.Program
