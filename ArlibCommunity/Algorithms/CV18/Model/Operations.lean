/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Model.Prelude
import Arlib.Computation.Charged

/-!
# Operations: the membership-query currency

**The resource claimed** (Theorem 1.1): the number of membership-oracle calls.  Each
call costs one.  Random numbers are tallied but not counted, and arithmetic is free: the
paper charges nothing for it and no machine model is claimed.

Arlib's standard currency (`StdOp`) has no membership queries, so this file declares a
local one:

* `Op` — one charged primitive: `query`, one membership-oracle call, and `draw`, one
  read of the random tape.
* `queryCount` — the query count of a tally: its `query` entry.  Draws are tallied, so
  the program cannot read randomness for free, but they are not counted.
* `Round n`, `Tape n` — one round of random numbers, and the tape: a round for every
  `i : ℕ`.  A round holds a point of the closed unit ball, a standard Gaussian vector and
  a number in `[0, 1]`; `Model/Run.lean` draws the rounds independently from those laws.
* `Oracle n` — **the sealed oracle**: the membership answers of the body, and the tape.
  Its fields are private and its constructor is the noncomputable boundary
  `Oracle.ofTape`, used only by `Model/Run.lean`.
* `ask`, `drawBall`, `drawGaussian`, `drawUnit` — the only ways to learn anything from an
  oracle.  `ask x` answers whether `x` is in the body and charges one `query`; each draw
  reads one component of the current round, moves the tape on by one round, and charges
  one `draw`.

Because every draw consumes a fresh round and the rounds are independent, each random
number the program reads is fresh: distributed as its law, independently of everything
the program has seen.  `Analysis/TapeLaw.lean` proves this.

Operations are vocabulary, not evidence: nothing here asserts a bound.
-/

set_option autoImplicit false

namespace ArlibCommunity.Algorithms.CV18.Model.Operations

open Arlib.Computation

/-- The storage currency.  No space bound is claimed, so it has one kind. -/
inductive Cell
  | cell
  deriving DecidableEq

/-- **One charged primitive**: a membership-oracle call `query` (one query), or one read
of the random tape `draw` (tallied, not counted as a query). -/
inductive Op
  | query
  | draw
  deriving DecidableEq

/-- The programs of this development: charged computations in the query currency. -/
abbrev Prog := Charged Op Cell

/-- **The query count of a tally**: every membership call counts one; draws count
zero. -/
def queryCount (c : CostVec Op) : ℕ := c .query

/-- One round of random numbers: a point of the closed unit ball, a standard Gaussian
vector, and a number in `[0, 1]`.  The laws are fixed by `Model/Run.lean`. -/
abbrev Round (n : ℕ) := AmbientSpace n × AmbientSpace n × ℝ

/-- The random tape: one round for every `i : ℕ`. -/
abbrev Tape (n : ℕ) := ℕ → Round n

/-- The tape after its first round has been read. -/
def Tape.tail {n : ℕ} (t : Tape n) : Tape n := fun i => t (i + 1)

/-- **The sealed oracle.**  The membership answers of the body (`member`), and the random
tape.  The fields are private: outside this module the only access is `ask` and the
draws, each of which charges one operation. -/
structure Oracle (n : ℕ) where
  private mk ::
  private member : AmbientSpace n → Bool
  private tape : Tape n

/-- The oracle answering membership by `member`, with random tape `tape`.  **The
boundary**: noncomputable, so a program cannot build the oracle it wants;
`Model/Run.lean` supplies the body's answers and draws the tape. -/
noncomputable def Oracle.ofTape {n : ℕ} (member : AmbientSpace n → Bool) (tape : Tape n) :
    Oracle n :=
  ⟨member, tape⟩

/-- **One membership call**: is `x` in the body?  Charges one `query`. -/
def ask {n : ℕ} (x : AmbientSpace n) (o : Oracle n) : Prog (Bool × Oracle n) :=
  Charged.op Op.query (o.member x, o)

/-- **A uniform point of the closed unit ball**: read the current round's point, move
the tape on, charge one `draw`. -/
def drawBall {n : ℕ} (o : Oracle n) : Prog (AmbientSpace n × Oracle n) :=
  Charged.op Op.draw ((o.tape 0).1, ⟨o.member, o.tape.tail⟩)

/-- **A standard Gaussian vector**: read the current round's vector, move the tape on,
charge one `draw`. -/
def drawGaussian {n : ℕ} (o : Oracle n) : Prog (AmbientSpace n × Oracle n) :=
  Charged.op Op.draw ((o.tape 0).2.1, ⟨o.member, o.tape.tail⟩)

/-- **A uniform number in `[0, 1]`**: read the current round's number, move the tape on,
charge one `draw`. -/
def drawUnit {n : ℕ} (o : Oracle n) : Prog (ℝ × Oracle n) :=
  Charged.op Op.draw ((o.tape 0).2.2, ⟨o.member, o.tape.tail⟩)

/-! The operations on an oracle built by `Oracle.ofTape`.  These are the only facts about
the private fields that the analysis uses. -/

theorem ask_ofTape {n : ℕ} (member : AmbientSpace n → Bool) (t : Tape n)
    (x : AmbientSpace n) :
    ask x (Oracle.ofTape member t) = Charged.op Op.query (member x, Oracle.ofTape member t) :=
  rfl

theorem drawBall_ofTape {n : ℕ} (member : AmbientSpace n → Bool) (t : Tape n) :
    drawBall (Oracle.ofTape member t) =
      Charged.op Op.draw ((t 0).1, Oracle.ofTape member t.tail) :=
  rfl

theorem drawGaussian_ofTape {n : ℕ} (member : AmbientSpace n → Bool) (t : Tape n) :
    drawGaussian (Oracle.ofTape member t) =
      Charged.op Op.draw ((t 0).2.1, Oracle.ofTape member t.tail) :=
  rfl

theorem drawUnit_ofTape {n : ℕ} (member : AmbientSpace n → Bool) (t : Tape n) :
    drawUnit (Oracle.ofTape member t) =
      Charged.op Op.draw ((t 0).2.2, Oracle.ofTape member t.tail) :=
  rfl

end ArlibCommunity.Algorithms.CV18.Model.Operations
