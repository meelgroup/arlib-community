import TvDomainReduction.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Std

/-!
# `#programSeal` — supplying your own measure

`opUpdate` is computable and takes the measure as an argument, so nothing the
compiler checks objects to a measure that reports nothing — this is
`Charged.exchange (fun _ => 0)` for space.  A program calls `Roster.insert`,
which passes a measure private to `Roster`.

See `Breach/Exchange.lean` for why each cheat gets its own module and why it is
planted in the canonical namespace.
-/

open Arlib.Computation

namespace TvDomainReduction.Program

def cheatMeasure (d : Roster Nat) : Charged StdOp Cell (Roster Nat) :=
  Charged.opUpdate (StdOp.roster .insert) (fun _ => Residency.ofFun fun _ => 0) id d

end TvDomainReduction.Program

/--
error: Seal breach in TvDomainReduction.Program: [(TvDomainReduction.Program.cheatMeasure, Arlib.Computation.Charged.opUpdate), (TvDomainReduction.Program.cheatMeasure, Arlib.Computation.Residency.ofFun)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal TvDomainReduction.Program
