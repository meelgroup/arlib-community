import Esa22Copy.Meta.CostSeal
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

Every seal cheat gets its **own module** under `Esa22CopyTest/Breach/`.
`#programSeal` scans only the canonical namespace `Esa22Copy.Program`, so a cheat
must be declared there to be seen, and one module per cheat keeps each expected
message a single entry and the tests independent of the order they run in.

## What is covered

* §1 — the cheats the *compiler* rejects, so that a change making one of them
  compile is caught before either seal is reached.
* §2 — further reads the compiler rejects (the sampling level, a profile, a
  residency).
* §3 — `#programSeal` refuses a non-canonical namespace and a vacuous scan.
* `Esa22CopyTest/Breach/` — `#programSeal`: the routes past the compiler, inside
  the algorithm — including the one that only a *transitive* scan catches
  (`Breach/Transitive.lean`), which is the property `reaches` exists for and the
  first test to run if it is ever touched.
The positive direction is covered by the main build: `Model/Program.lean` runs
the command over the real algorithm and it reports clean.
-/

namespace Esa22CopyTest

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

/-! ## 2. More that the compiler rejects -/

/-! **Reading the sampling level.**  The level is inside a `Sampler` and
`Sampler.levelOf` is noncomputable, so the compiler rejects this before the seal
gets to it — which is the stronger of the two rejections.  With `level : ℕ` a
bare field, `|X| * 2 ^ level` was the driver's arithmetic on a number nobody
asked for. -/
namespace Breach.PeekLevel.Program
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Sampler.levelOf', which is 'noncomputable'
-/
#guard_msgs in
def cheat (s : Sampler) (n : Nat) : Nat := n * 2 ^ s.levelOf
end Breach.PeekLevel.Program

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

/-! ## 3. `#programSeal` refuses to be pointed elsewhere

The seal accepts exactly one namespace, `Esa22Copy.Program`, so it cannot be
quietly retargeted at a namespace where nothing lives, and it refuses a scan that
checks nothing.  The planted breaches themselves are in `Esa22CopyTest/Breach/`,
one module each: a cheat has to be declared under `Esa22Copy.Program` for the
seal to look at it, and Lean cannot remove a declaration once made, so a second
cheat in this file would appear in every later test's message. -/

/--
error: Program seal must target the canonical namespace Esa22Copy.Program, not Esa22CopyTest.Elsewhere.Program.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22CopyTest.Elsewhere.Program

/--
error: Program seal checked zero declarations under Esa22Copy.Program.  Put the executable declarations from Model/Program.lean in this exact namespace; a vacuous seal is not a seal.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program

end Esa22CopyTest
