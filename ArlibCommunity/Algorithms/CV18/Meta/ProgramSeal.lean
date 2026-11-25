/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Arlib.Computation.Charged

/-!
# `#programSeal`: the program learns nothing for free

Machine-checks that the algorithm of `Model/Program.lean` pays for what it learns.  A
command, so it fires on every build; placed here because it is tooling, outside the
surface it checks (as `ModelClosure` is).

## What the compiler already does

`Arlib.Computation.Charged` has a private constructor, so a program's tally is a function
of its text: `pure` is free, `bind` adds, `Charged.op` charges one.  The oracle
(`Model/Operations.lean`) has private fields and a noncomputable constructor, so a
program cannot name the body's membership answers or the random tape; it reaches them
only through `ask` and the draws, each of which charges one operation.

## What this additionally checks

A structure's `casesOn` and `rec` are generated public even when its fields are private,
so a determined author could project a private field out; and a program could re-price
its own tally (`Charged.exchange`), read it (`Charged.cost`), take a computation's value
without binding it (`Charged.val`), or charge a hand-written operation inline
(`Charged.op`).  `#programSeal` rejects every declaration of the program namespace that
reaches one of these, **transitively**: through any chain of definitions, stopping only
at the sanctioned vocabulary (the monad structure of `Charged`, and the operations of
`Model/Operations.lean`).

## The one difference from a rational-arithmetic program

CV18's arithmetic is on real numbers (`ℝ`), which Lean cannot run, so the program is
`noncomputable` and this seal does not ask it to be computable.  Computability is not
what makes the seal sound: what matters is that the program cannot reach the oracle's
private fields or a computation's value or tally except through charged operations, and
that is checked by name, transitively, below.
-/

open Lean Elab Command

namespace ArlibCommunity.Algorithms.CV18.Meta

/-- Constants an algorithm may not mention.  The eliminators the compiler generates
public for the sealed carriers; the reads of a computation's value and tally; the
re-pricing and hand-charging escape hatches of `Charged`; and the oracle's constructor. -/
def forbiddenInProgram : List Name :=
  [``Arlib.Computation.Charged.casesOn, ``Arlib.Computation.Charged.rec,
   ``Arlib.Computation.Charged.recOn,
   ``Arlib.Computation.Charged.val, ``Arlib.Computation.Charged.cost,
   ``Arlib.Computation.Charged.space, ``Arlib.Computation.Charged.steps,
   ``Arlib.Computation.Charged.exchange, ``Arlib.Computation.Charged.opUpdate,
   ``Arlib.Computation.Charged.peakAt, ``Arlib.Computation.Charged.netAt,
   -- **and `Charged.op` itself, except behind the operations of
   -- `Model/Operations.lean`.**  `Charged.op o a` charges one operation for a value the
   -- program computed for itself; the operations a line of the paper's pseudocode may
   -- perform are named in `Model/Operations.lean`, not inline in the program.
   ``Arlib.Computation.Charged.op, ``Arlib.Computation.Charged.opMany,
   `ArlibCommunity.Algorithms.CV18.Model.Operations.Oracle.casesOn,
   `ArlibCommunity.Algorithms.CV18.Model.Operations.Oracle.rec,
   `ArlibCommunity.Algorithms.CV18.Model.Operations.Oracle.recOn,
   -- a program that could build its own oracle could choose the answers and the tape
   `ArlibCommunity.Algorithms.CV18.Model.Operations.Oracle.ofTape]

/-- The sealed carriers.  A private declaration under one of these (a field, the
constructor) is forbidden wherever it is reached from, except through the sanctioned
vocabulary below. -/
def sealedCarriers : List Name :=
  [``Arlib.Computation.Charged, `ArlibCommunity.Algorithms.CV18.Model.Operations.Oracle]

/-- **The frontier the transitive walk stops at: the vocabulary an algorithm may use.**
The monad structure of `Charged` (built from its private constructor, and audited by
arlib), and every declaration of `Model/Operations.lean`, the currency the paper counts
in.  The walk does not enter these: their internals are not the program's. -/
def sanctioned : List Name :=
  [``Arlib.Computation.Charged.pure, ``Arlib.Computation.Charged.bind]

/-- Project-local primitive wrappers: the operations of `Model/Operations.lean`. -/
def sanctionedPrefixes : List Name :=
  [`ArlibCommunity.Algorithms.CV18.Model.Operations]

/-- Is `c` forbidden in a program? -/
private def isForbidden (c : Name) : Bool :=
  forbiddenInProgram.contains c ||
    (isPrivateName c &&
      sealedCarriers.any fun s => s.isPrefixOf (privateToUserName c))

/-- INTERNAL: is `c`'s type a `Prop`?  A proof computes nothing, so what it mentions is
not work a program performs. -/
private def isPropConst (c : Name) : CommandElabM Bool := do
  match (← getEnv).find? c with
  | some ci => liftTermElabM (Lean.Meta.isProp ci.type)
  | none => return true

/-- **Does `c` reach a forbidden constant?**  Transitively, through values; stopping at
the sanctioned vocabulary and at proofs.  `memo` makes the walk linear, and a constant is
memoised `false` before its successors are explored, which stops the recursion on
cycles. -/
private partial def reaches (memo : Std.HashMap Name Bool) (c : Name) :
    CommandElabM (Bool × Std.HashMap Name Bool) := do
  if let some b := memo[c]? then return (b, memo)
  if isForbidden c then return (true, memo.insert c true)
  if sanctioned.contains c || sanctionedPrefixes.any (fun p => p.isPrefixOf c) then
    return (false, memo.insert c false)
  let mut m := memo.insert c false
  let mut hit := false
  if !(← isPropConst c) then
    if let some ci := (← getEnv).find? c then
      if let some v := ci.value? then
        for u in v.getUsedConstants do
          if !hit then
            let (h, m') ← reaches m u
            m := m'
            hit := h
  return (hit, m.insert c hit)

/-- The scanner behind `#programSeal`. -/
private def runProgramSeal (ns : Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  let mut count : Nat := 0
  let mut memo : Std.HashMap Name Bool := {}
  for (c, ci) in env.constants.toList do
    if c.isInternal then continue
    unless ns.isPrefixOf c do continue
    if ← liftTermElabM (Lean.Meta.isProp ci.type) then continue
    count := count + 1
    match ci.value? with
    | some v =>
        for u in v.getUsedConstants do
          if isForbidden u then
            bad := bad.push (c, u)
          else
            let (hit, memo') ← reaches memo u
            memo := memo'
            if hit then bad := bad.push (c, u)
    | none => pure ()
  if count == 0 then
    throwError m!"Program seal checked zero declarations under {ns}: a vacuous seal is \
      not a seal."
  unless bad.isEmpty do
    throwError m!"Seal breach in {ns}: {bad.toList}.  A program that reads the oracle, \
      a computation's value or its tally without a charged operation can learn what it \
      does not pay for."
  logInfo m!"Program seal: {count} declarations under {ns}, none reaching the oracle's \
    private fields, a computation's value or tally, or a hand-charged operation \
    (transitively, through {memo.size} constants)."

/-- **The algorithm may not learn for free.**  Checks every non-`Prop` declaration under
the program namespace `ArlibCommunity.Algorithms.CV18.Program`. -/
elab "#programSeal " id:ident : command => do
  let ns := id.getId
  let canonical := `ArlibCommunity.Algorithms.CV18.Program
  unless ns == canonical do
    throwError m!"Program seal must target the canonical namespace {canonical}, not {ns}."
  runProgramSeal ns

/-- INTERNAL TEST COMMAND: run the scanner on a planted breach, outside the canonical
namespace. -/
elab "#programSealFixture " id:ident : command => do
  let ns := id.getId
  let fixtures := `ArlibCommunityTest.CV18.Breach
  unless fixtures.isPrefixOf ns do
    throwError m!"Program seal fixtures must be under {fixtures}, not {ns}."
  runProgramSeal ns

/-- **Everything in the algorithm's module is part of the algorithm.**

Checks every author-written declaration *defined in a module under `mod`* (theorems
skipped: a proof computes nothing):

* it lies in the canonical program namespace `ArlibCommunity.Algorithms.CV18.Program`, so
  `#programSeal`, which guards that namespace, sees it;
* it is not a specification — a `def` whose result is a `Prop`, or a `Set`, which is a
  `Prop`-valued function wearing other clothes.  A specification is a sentence about the
  algorithm, not a line of it, and belongs in `Model/Prelude.lean`.

**What this does not check, unlike barbarik4's version: that the declarations are
computable.**  CV18's arithmetic is on real numbers, which Lean cannot run, so every
procedure is `noncomputable`.  In barbarik4 the computability check also closes the
route of a `noncomputable def` reading `Charged.val`; here `#programSeal` forbids
`Charged.val`, and the oracle's private fields, by name and transitively, which closes
that route without it. -/
elab "#executableModule " mod:ident : command => do
  let prefix_ := mod.getId
  let programNs := `ArlibCommunity.Algorithms.CV18.Program
  let env ← getEnv
  let mut bad : Array (Name × String) := #[]
  let mut count : Nat := 0
  for (c, ci) in env.constants.toList do
    if c.isInternal then continue
    unless (`ArlibCommunity).isPrefixOf c do continue
    match env.getModuleIdxFor? c with
    | some idx =>
        unless prefix_.isPrefixOf ((env.allImportedModuleNames[idx.toNat]?).getD `«unknown») do
          continue
    | none => unless prefix_.isPrefixOf env.mainModule do continue
    if ci.isTheorem then continue
    if ← liftTermElabM (Lean.Meta.isProp ci.type) then continue
    count := count + 1
    unless programNs.isPrefixOf c do
      bad := bad.push (c, s!"outside canonical program namespace {programNs}")
    if ← liftTermElabM (Lean.Meta.forallTelescopeReducing ci.type fun _ body => do
        return (← Lean.Meta.whnf body).isProp) then
      bad := bad.push (c, "specification, not a program")
  unless bad.isEmpty do
    throwError m!"Not part of the algorithm in {prefix_}: {bad.toList}.  This module is \
      the algorithm; move a specification to `Model/Prelude.lean` and anything else out \
      of the module."
  logInfo m!"Algorithm module: {count} definitions in {prefix_}, all in {programNs}, \
    none a specification (computability not required: the arithmetic is on `ℝ`)."

end ArlibCommunity.Algorithms.CV18.Meta
