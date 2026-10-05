import TvDomainReduction.Meta.CostSeal
import Arlib.Computation.Roster
import Arlib.Computation.Std

/-!
# `#programSeal` — projecting a dictionary's contents through the eliminator

`casesOn` is generated public even though the constructor is private, and it is
compiled, so this is the one route the compiler genuinely leaves open.

See `Breach/Exchange.lean` for why each cheat gets its own module and why it is
planted in the canonical namespace.
-/

open Arlib.Computation

namespace TvDomainReduction.Program

def cheatCasesOn (d : Roster Nat) : Nat :=
  Roster.casesOn (motive := fun _ => Nat) d (fun elems _ => elems.length)

end TvDomainReduction.Program

/--
error: Seal breach in TvDomainReduction.Program: [(TvDomainReduction.Program.cheatCasesOn, Arlib.Computation.Roster.casesOn)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal TvDomainReduction.Program
