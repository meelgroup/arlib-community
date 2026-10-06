import TvDomainReduction.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Std

/-!
# `#programSeal` — reading the measured peak

`Charged.peakAt` is computable on purpose — `#guard` has to read it for the
protocol's execution tests — so the compiler does not object, and the seal is
what stops an algorithm from using it as a free size query.  Same standing as
`Charged.cost`.

See `Breach/Exchange.lean` for why each cheat gets its own module and why it is
planted in the canonical namespace.
-/

open Arlib.Computation

namespace TvDomainReduction.Program

def cheatPeakAt (p : Charged StdOp Cell Nat) : Int := p.peakAt Cell.cell

end TvDomainReduction.Program

/--
error: Seal breach in TvDomainReduction.Program: [(TvDomainReduction.Program.cheatPeakAt, Arlib.Computation.Charged.peakAt)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal TvDomainReduction.Program
