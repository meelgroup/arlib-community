import TvDomainReduction.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# The seal, made to fail

`Model/Program.lean` runs `#programSeal` on every build, and it passes.  That
is not evidence.  An audit that has never rejected anything is
not known to reject anything, and the two commands are exactly the kind of code
whose failure mode is silence — a filter that matches nothing reports a clean
build.

Each test below is a `#guard_msgs` block: it **passes when the checker produces
exactly the stated error**, so a future change that quietly opens one of these
routes turns this file red.  This is the same discipline as
`ArlibTest/Computation.lean` §3, applied to the checkers rather than to the
compiler.

## Why the `#programSeal` tests are one module each

`#programSeal` takes a namespace, and it refuses any namespace but the canonical
`TvDomainReduction.Program` — a seal that can be pointed somewhere harmless is
not a seal, so the command checks its own target.  A planted cheat therefore has
to go in that one namespace, and the *module* is what separates one cheat from
the next: a second cheat in the same file would appear in the first test's
expected message too, and the order the two appear in is a hash-table order
nobody should be asserting.  So §2 lives in `TvDomainReductionTest/Breach/`, one
breach per module:

| route past the compiler | module |
| --- | --- |
| `Charged.exchange` at rate zero | `Breach/Exchange.lean` |
| `noncomputable def` | `Breach/Noncomputable.lean` |
| `Roster.casesOn` | `Breach/CasesOn.lean` |
| `Charged.op` inline | `Breach/HandPriced.lean` |
| `Charged.cost` | `Breach/Cost.lean` |
| `Charged.steps`, caught only transitively | `Breach/Transitive.lean` |
| `Charged.opUpdate` with a private measure | `Breach/Measure.lean` |
| `Charged.peakAt` | `Breach/PeakAt.lean` |

None of those modules imports `Model/Program.lean`, so the seal sees the planted
cheat and nothing else.  The positive direction is covered by the main build:
`Model/Program.lean` runs the command over the real algorithm and it reports
clean.

## What this file covers

The cheats the *compiler* rejects, so that a change making one of them compile is
caught before either seal is reached.
-/

namespace TvDomainReductionTest

open Arlib.Computation

/-! ## 1. What the compiler rejects on its own -/

/-! Copying a computation's result to drop its charges.  This is the cheat that
would make every bound in the development vacuous, and it does not compile,
because `Charged.val` is `noncomputable`. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.val', which is 'noncomputable'
-/
#guard_msgs in
def dropTally (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat := pure p.val

/-! Reading a dictionary's size without asking it.  `Roster.card` is the
specification's view and is `noncomputable`, so a program that wants the number
must call `Roster.size` and pay. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Roster.card', which is 'noncomputable'
-/
#guard_msgs in
def freeSize (d : Roster Nat) : Nat := d.card

/-! Forging a tally.  There is no syntax for asserting what something cost. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Arlib.Computation.Charged` is marked as private
-/
#guard_msgs in
example : Charged StdOp Cell Nat := ⟨0, 0, 1⟩

/-! **Reading the sampling level.**  The level is inside a `Sampler` and
`Sampler.levelOf` is noncomputable, so the compiler rejects this before the seal
gets to it — which is the stronger of the two rejections.  With `level : ℕ` a
bare field, `|X| * 2 ^ level` was the driver's arithmetic on a number nobody
asked for. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Sampler.levelOf', which is 'noncomputable'
-/
#guard_msgs in
def peekLevel (s : Sampler) (n : Nat) : Nat := n * 2 ^ s.levelOf

/-! **Reading what a computation holds.**  This one the compiler rejects on its
own, and for a stronger reason than it rejects `Charged.cost`: a tally tells a
program which branch it took, which it already knew, while a profile tells it how
much data it holds — which is exactly what the data seal hides.  `decide
(p.space.net k = 1)` after an insertion is a free membership test. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.space', which is 'noncomputable'
-/
#guard_msgs in
def readProfile (p : Charged StdOp Cell Nat) : Profile Cell := p.space

/-! **Measuring a dictionary directly.**  `Residency.at'` is the space analogue
of `Roster.card`, and noncomputable for the same reason. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Residency.at'', which is 'noncomputable'
-/
#guard_msgs in
def readResidency (r : Residency Cell) : Nat := r.at' Cell.cell

end TvDomainReductionTest
