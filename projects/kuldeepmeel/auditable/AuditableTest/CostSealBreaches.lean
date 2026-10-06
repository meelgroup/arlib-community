import Auditable.Meta.CostSeal
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

`#programSeal` accepts exactly one namespace, `Auditable.Program` — the one the
algorithm lives in — and refuses any other, so a cheat cannot be audited
somewhere the real program is not.  Every cheat below is therefore planted in
`Auditable.Program` itself, inside a `#breach … #endBreach` block that discards
the declarations it made once it closes.  Each test sees exactly one cheat, which
keeps each expected message a single entry and keeps the tests independent of
the order they run in.  The block restores the environment and nothing else: the
seal runs on the cheat exactly as it would on `Model/Program.lean`.

## What is covered

* §1 — the cheats the *compiler* rejects, so that a change making one of them
  compile is caught before either seal is reached.
* §2 — `#programSeal`: the routes past the compiler, inside the algorithm —
  including the one that only a *transitive* scan catches, which is the property
  `reaches` exists for and the first test to run if it is ever touched.
* §3 — `#programSeal` refuses to be pointed anywhere else, and refuses to pass
  vacuously.
The positive direction is covered by the main build: `Model/Program.lean` runs
the command over the real algorithm and it reports clean.
-/

namespace AuditableTest

open Arlib.Computation

open Lean Elab Command in
/-- Elaborate the enclosed commands, then restore the environment they started
from, so that a cheat planted in `Auditable.Program` is gone before the next
test plants its own.

Each enclosed command gets a message log of its own.  Without that the whole
block is one command, and a `#guard_msgs` inside it would consume the errors of
every command before it — a cheat that failed to elaborate would vanish without
a word. -/
elab "#breach " cmds:command* " #endBreach" : command => do
  let env ← getEnv
  try
    for c in cmds do
      let prior ← modifyGet fun st => (st.messages, { st with messages := {} })
      try elabCommand c
      finally modify fun st => { st with messages := prior ++ st.messages }
  finally
    setEnv env

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

end AuditableTest

/-! ## 2. `#programSeal` — the routes past the compiler

From here on the file is outside `namespace AuditableTest`, because a cheat has
to be planted in `Auditable.Program` itself and Lean has no `_root_` form of
`namespace`.  The declarations that only the compiler is asked about keep an
`AuditableTest.` name. -/

open Arlib.Computation

/-! **Laundering a tally through a change of currency.**  `exchange` is
computable and takes a `Charged` to a `Charged`, so nothing the compiler checks
stands in the way; at a rate of zero it re-prices any computation at nothing. -/
#breach
namespace Auditable.Program
def cheat (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat :=
  Charged.exchange (fun _ => (0 : CostVec StdOp)) p
end Auditable.Program

/--
error: Seal breach in Auditable.Program: [(Auditable.Program.cheat, Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Auditable.Program
#endBreach

/-! **Silencing the compiler.**  Writing `noncomputable def` turns off the half
of the seal §1 relies on.  Nothing else about this declaration is wrong, which is
the point: the marker alone is the breach. -/
#breach
namespace Auditable.Program
noncomputable def cheat_proof : Real := 0
end Auditable.Program

/--
error: Seal breach in Auditable.Program: [(Auditable.Program.cheat_proof, noncomputableProgram)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Auditable.Program
#endBreach

/-! **Projecting a dictionary's contents through the eliminator.**  `casesOn` is
generated public even though the constructor is private, and it is compiled, so
this is the one route the compiler genuinely leaves open. -/
#breach
namespace Auditable.Program
def cheat_proof2 (d : Roster Nat) : Nat :=
  Roster.casesOn (motive := fun _ => Nat) d (fun elems _ => elems.length)
end Auditable.Program

/--
error: Seal breach in Auditable.Program: [(Auditable.Program.cheat_proof2, Arlib.Computation.Roster.casesOn)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Auditable.Program
#endBreach

/-! **Pricing a line by hand.**  `Charged.op o a` is arlib's escape hatch — one
operation of the currency, returning a value the algorithm computed for itself —
and a program may not call it inline. Standard operations come from arlib;
project-local operations come from `Model/Operations.lean`.

The cheat below is exactly what the algorithm used to do, and it is the shape to
watch for: the charge says "one coin" and the argument is an `O(level)` scan of a
bare bit block, read at a level nobody paid for.  The seal cannot see that the
argument is expensive — nothing can — so it forbids the escape hatch directly in
`Program.lean`. The honest fix for a line that genuinely needs one is to expose
the primitive in the operation model. -/
#breach
namespace Auditable.Program
-- The original wrote this against the development's own `BitBlock` and
-- `acceptsAt`, which is the shape the algorithm actually had. Here it is a
-- bare function on `Nat`, so that the breach library builds with nothing but
-- arlib and can be a default target from the first commit of a project. The
-- property under test is unchanged: the charge says one coin, and the seal
-- cannot see what the argument cost.
def cheat_proof3 (level : Nat) (bits : Nat → Bool) : Charged StdOp Cell Bool :=
  Charged.op (StdOp.rand .accept) (bits level)
end Auditable.Program

/--
error: Seal breach in Auditable.Program: [(Auditable.Program.cheat_proof3, Arlib.Computation.Charged.op)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Auditable.Program
#endBreach

/-! **Reading the sampling level.**  The level is inside a `Sampler` and
`Sampler.levelOf` is noncomputable, so the compiler rejects this before the seal
gets to it — which is the stronger of the two rejections.  With `level : ℕ` a
bare field, `|X| * 2 ^ level` was the driver's arithmetic on a number nobody
asked for. -/
namespace AuditableTest.Breach.PeekLevel.Program
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Sampler.levelOf', which is 'noncomputable'
-/
#guard_msgs in
def cheat (s : Sampler) (n : Nat) : Nat := n * 2 ^ s.levelOf
end AuditableTest.Breach.PeekLevel.Program

/-! **Observing a computation's own tally.**  `Charged.cost` is computable and
"produces no value" — until `decide` is applied to it.  `Roster.cost_filterErase`
equates a thinning pass's tally to `d.card`, so a program that may read `cost`
has a free cardinality and therefore a free `cardEq`. -/
#breach
namespace Auditable.Program
def cheat_proof4 (p : Charged StdOp Cell Nat) : CostVec StdOp := p.cost
end Auditable.Program

/--
error: Seal breach in Auditable.Program: [(Auditable.Program.cheat_proof4, Arlib.Computation.Charged.cost)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Auditable.Program
#endBreach

/-! **The same read, one hop away.**  `Charged.steps` is deliberately absent from
`forbiddenInProgram`: it is `CostVec.steps C p.cost`, so a blacklist of *direct*
mentions would miss it entirely.  This test is what makes the transitive walk a
checked fact rather than an intention, and it is the one to run first if
`reaches` is ever changed.

Note which constant the message names — the intermediary the program actually
called, not the forbidden constant behind it.  That is the name whose call site
has to change. -/
#breach
namespace Auditable.Program
def cheat_proof5 (p : Charged StdOp Cell Nat) : Nat := Charged.steps (Rate.unit StdOp) p
end Auditable.Program

/--
error: Seal breach in Auditable.Program: [(Auditable.Program.cheat_proof5, Arlib.Computation.Charged.steps)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Auditable.Program
#endBreach

/-! **Reading what a computation holds.**  This one the compiler rejects on its
own, and for a stronger reason than it rejects `Charged.cost`: a tally tells a
program which branch it took, which it already knew, while a profile tells it how
much data it holds — which is exactly what the data seal hides.  `decide
(p.space.net k = 1)` after an insertion is a free membership test. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.space', which is 'noncomputable'
-/
#guard_msgs in
def AuditableTest.readProfile (p : Charged StdOp Cell Nat) : Profile Cell := p.space

/-! **Measuring a dictionary directly.**  `Residency.at'` is the space analogue
of `Roster.card`, and noncomputable for the same reason. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Residency.at'', which is 'noncomputable'
-/
#guard_msgs in
def AuditableTest.readResidency (r : Residency Cell) : Nat := r.at' Cell.cell

/-! **Supplying your own measure.**  `opUpdate` is computable and takes the
measure as an argument, so nothing the compiler checks objects to a measure that
reports nothing — this is `Charged.exchange (fun _ => 0)` for space.  A program
calls `Roster.insert`, which passes a measure private to `Roster`. -/
#breach
namespace Auditable.Program
def cheat_proof6 (d : Roster Nat) : Charged StdOp Cell (Roster Nat) :=
  Charged.opUpdate (StdOp.roster .insert) (fun _ => Residency.ofFun fun _ => 0) id d
end Auditable.Program

/--
error: Seal breach in Auditable.Program: [(Auditable.Program.cheat_proof6, Arlib.Computation.Charged.opUpdate), (Auditable.Program.cheat_proof6, Arlib.Computation.Residency.ofFun)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Auditable.Program
#endBreach

/-! **Reading the measured peak.**  `Charged.peakAt` is computable on purpose —
`#guard` has to read it for the protocol's execution tests — so the compiler does
not object, and the seal is what stops an algorithm from using it as a free size
query.  Same standing as `Charged.cost`. -/
#breach
namespace Auditable.Program
def cheat_proof7 (p : Charged StdOp Cell Nat) : Int := p.peakAt Cell.cell
end Auditable.Program

/--
error: Seal breach in Auditable.Program: [(Auditable.Program.cheat_proof7, Arlib.Computation.Charged.peakAt)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Auditable.Program
#endBreach

/-! ## 3. `#programSeal` — where it may be pointed

The seal is not a function of its argument: it audits `Auditable.Program` or it
refuses.  An author who moved the algorithm into another namespace, and pointed
the command there, would otherwise be auditing nothing in particular. -/
/--
error: Program seal must target the canonical namespace Auditable.Program, not AuditableTest.Breach.Exchange.Program.
-/
#guard_msgs in
#programSeal AuditableTest.Breach.Exchange.Program

/-! And a seal over an empty namespace is not a pass.  Every breach above has
been discarded, so `Auditable.Program` holds nothing here. -/
/--
error: Program seal checked zero declarations under Auditable.Program.  Put the executable declarations from Model/Program.lean in this exact namespace; a vacuous seal is not a seal.
-/
#guard_msgs (whitespace := lax) in
#programSeal Auditable.Program
