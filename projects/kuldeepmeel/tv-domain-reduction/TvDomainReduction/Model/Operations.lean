import Arlib.Computation.Charged
import Arlib.Computation.Std

/-!
# The currency the paper counts in: arithmetic operations on reals

Theorem 4.1 bounds an **arithmetic running time** (main.tex:904): operations on
exact real numbers, in the arithmetic / real-RAM model the paper calls "strongly
polynomial in the real-arithmetic model" (main.tex:147).  arlib's
`Arlib.Computation.Op` is a *word* RAM, and arlib's `StdOp` is the vocabulary of
its sealed containers; neither is what the paper charges.  Charging word
operations would be a different claim, and for real-valued Lewis weights a
meaningless one.

So this file declares a project-local work currency `ArithOp` and uses arlib's
currency-generic layer (`CostVec`, `Charged`, `Rate`, `worstSteps`) on top of it.
The storage currency is arlib's `Cell`: the paper makes no space claim, and one
kind of cell — a retained coreset row — is all the vocabulary needed to state
one if a later pass wants it.

## What each operation is

`add`, `sub`, `mul`, `div`, `abs`, `cmp` are the arithmetic primitives on reals.
`lit` is reading one stored real (a leaf-table entry, a coefficient-tensor
entry, a weight).  The paper never fixes its operation set — main.tex:904 says
"arithmetic running time" and nothing more — so this list is a **decision**, and
it is deliberately the maximal reasonable one: every question the algorithm asks
of a real number, including a comparison and an absolute value, is charged, so
nothing it does is free.

`lewis` is **one arithmetic operation performed inside the cited Lewis-weight
solver** (main.tex:751, cited to Lee–Sidford Thm 5.3.1 and Jambulapati et al.
Lemma 2.5).  It is a primitive and not a composite: the *number* of them a call
performs is `SparsifyPrior.callCost N d`, a field of the prior, and the paper's
`Õ(N d + d^ω)` is `SparsifyPrior.callCost_le`, a promise the prior makes.  One
`lewis` buys one operation, so `lewisOps n` pays `n` of them and no amount of
work hides behind a single token.  This is the only honest shape available: the
paper cites the solver rather than giving it, so its internals are not this
development's to charge line by line, and the thing that must be visible is how
many operations are being bought and on whose authority.

`ω` itself is **not** here: it is `SparsifyPrior.mmExp`, a parameter of the
theorem with `2 ≤ ω ≤ 2.4` as a field, because it is an external constant about
matrix multiplication and not a price this development sets.

## Why the rate is the unit rate

The paper counts operations, each once.  `Rate.unit ArithOp` is exactly that, and
`Rate`'s `one_le` field means no operation can be priced at zero.  Nothing
asymptotic is baked in anywhere: every suppressed constant and polylog in the
running-time claim is a field of `SparsifyPrior`, not a numeral here.

## The charged wrappers

Every charge in `Model/Program.lean` goes through one of the wrappers below.
That is not decoration: `Meta/CostSeal.lean` puts `Charged.op` and
`Charged.opMany` on `forbiddenInProgram` and admits them only under the
namespace `TvDomainReduction.Model.Operations`, so a hand-priced line inside the
program is a build error and the audited frontier for project-local primitives is
this file.
-/

set_option autoImplicit false

namespace TvDomainReduction.Model.Operations

open Arlib.Computation

/-! ## The work currency -/

/-- **One arithmetic operation on reals.**

`lit` is a read of one stored real; `lewis` is one arithmetic operation performed
inside the cited Lewis-weight solver (see the module docstring). -/
inductive ArithOp
  | add | sub | mul | div | abs | cmp | lit | lewis
  deriving DecidableEq, Repr, Inhabited

namespace ArithOp

/-- Every arithmetic operation, as a list.  Written out rather than derived, for
the same reason arlib writes `Op.all` out: the `deriving Fintype` handler does
not elaborate against the `Finset` API of this Mathlib revision. -/
def all : List ArithOp := [.add, .sub, .mul, .div, .abs, .cmp, .lit, .lewis]

/-- INTERNAL: `all` is exhaustive, which is what makes `Fintype` legal. -/
theorem mem_all (o : ArithOp) : o ∈ all := by cases o <;> simp [all]

/-- The currency is finite, so `CostVec.steps` can sum over it. -/
instance : Fintype ArithOp := Fintype.ofList all mem_all

end ArithOp

/-- **The storage currency**: one kind of cell, a retained coreset row.  arlib's
`Cell` is reused rather than re-declared, since there is one structure to hold. -/
abbrev Cell : Type := Arlib.Computation.Cell

/-- **The rate the theorem is stated against**: every arithmetic operation costs
one, which is what "arithmetic running time" means (main.tex:904). -/
def rate : Rate ArithOp := Rate.unit ArithOp

/-- A charged computation in this development's currency. -/
abbrev Comp (α : Type _) : Type _ := Charged ArithOp Cell α

/-! ## The charged primitive wrappers

Each takes the number of primitives performed and the value they produced.  The
value is not what is being paid for — the tally is — so these are `opMany`,
arlib's "`n` instances of one operation, whose count the program already knows".

There is a wrapper for every operation this program charges and no others.  `cmp`
is in the currency — the operation set is fixed by the model, not by the program —
but has no wrapper, because the propagation never branches on a real number.  A
future line that does compare adds the wrapper here, which is the point: the
charge for it cannot be invented inside `Program.lean`. -/

universe u

variable {α : Type u}

/-- `n` real additions. -/
def adds (n : ℕ) (a : α) : Comp α := Charged.opMany .add n a

/-- `n` real subtractions. -/
def subs (n : ℕ) (a : α) : Comp α := Charged.opMany .sub n a

/-- `n` real multiplications. -/
def muls (n : ℕ) (a : α) : Comp α := Charged.opMany .mul n a

/-- `n` real divisions. -/
def divs (n : ℕ) (a : α) : Comp α := Charged.opMany .div n a

/-- `n` absolute values. -/
def abses (n : ℕ) (a : α) : Comp α := Charged.opMany .abs n a

/-- `n` reads of stored reals: leaf-table entries, coefficient-tensor entries,
coreset weights. -/
def reads (n : ℕ) (a : α) : Comp α := Charged.opMany .lit n a

/-- `n` arithmetic operations performed inside the cited Lewis-weight solver
(main.tex:751).  The caller supplies `n` from `SparsifyPrior.callCost`; the
paper's `Õ(N d + d^ω)` bound on it is `SparsifyPrior.callCost_le`. -/
def lewisOps (n : ℕ) (a : α) : Comp α := Charged.opMany .lewis n a

end TvDomainReduction.Model.Operations
