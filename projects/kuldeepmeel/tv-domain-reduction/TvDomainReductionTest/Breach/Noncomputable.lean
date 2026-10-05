import TvDomainReduction.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Std

/-!
# `#programSeal` — silencing the compiler

Writing `noncomputable def` turns off the half of the seal that the
compiler-rejection tests in `CostSealBreaches.lean` §1 rely on.  Nothing else
about this declaration is wrong, which is the point: the marker alone is the
breach.

See `Breach/Exchange.lean` for why each cheat gets its own module and why it is
planted in the canonical namespace.
-/

namespace TvDomainReduction.Program

noncomputable def cheatNoncomputable : Real := 0

end TvDomainReduction.Program

/--
error: Seal breach in TvDomainReduction.Program: [(TvDomainReduction.Program.cheatNoncomputable, noncomputableProgram)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal TvDomainReduction.Program
