import Esa22Copy.Model.Program

/-!
# Encoding: how the analysis reads Algorithm 1's sealed carriers

Definitional glue between `Esa22Copy.Program` (Algorithm 1 over arlib's sealed
carriers) and the proofs that will reason about it with `Finset`, `ℕ` and `PMF`.
Every lemma here is `rfl`; anything that is not belongs in
`Interface/ProgramModel.lean`.  Nothing here charges, nothing here is run, and
no headline mentions any of it.

## 1. The class indirection, collapsed

The program is written against arlib's `RosterOps`/`RandOps`/`SlotOps`/
`RosterCells` classes; `Model/Operations.lean` instantiates them at arlib's
`StdOp` and `Cell`.  One `@[simp]` lemma per class turns `Roster.opcode StdOp o`,
`randOpcode StdOp o`, `slotOpcode StdOp o` and `Roster.cell (Fin n)` into the
constructors `StdOp.roster o`, `StdOp.rand o`, `StdOp.slot o` and `Cell.cell`.

## 2. The specification's views of a state

| paper | view of `s : Program.State n` |
|---|---|
| the sample `X` | `sample s = s.X.toFinset` |
| `p = 2⁻ᵏ` | `level s = s.rate.levelOf` (`p = 2^-(level s)`) |
| "⊥ has not been output" | `running s = s.bot.get.isNone` |

The pick of line 4 reads the first `k` bits of the item's block: `pickAccepts k b`
is that predicate, and `val_accept` is arlib's suggested one-line bridge to it
(`Sampler.val_accept` is deliberately not `simp`).  The thinning coins of line 6
are read through arlib's own `Coins.heads'` (`Coins.val_flip` is already `simp`).

## 3. Handles on `Model/Program.lean` subterms

| paper (Algorithm 1) | handle |
|---|---|
| one pass of lines 3-8 on item `aᵢ` with its draw | `stepState thr s ad = (Program.step thr s ad).val` |
| lines 2-10, from any state | `foldState thr l s` (`foldState_nil`, `foldState_cons`) |
| the state after the loop, from line 1's state | `finalState thr A tape` |
| line 11: `⊥` or `\|X\|/p = \|X\|·2ᵏ` | `answerOf s` |

**Not stated here:** `(Program.estimator thr A tape).val = answerOf (finalState thr A tape)`.
It is *not* `rfl` — `Charged.val` does not commute definitionally with the
program's `if` on an opaque condition — so it is a claim, and belongs to
`Interface/ProgramModel.lean` (it closes by unfolding, `rw [Charged.val_bind]`,
`split`, `rw [Slot.val_isEmpty] at h`, then `if_pos`/`if_neg` and `rfl`).

`answerOf` reads `s.X.card` (the roster's own count, which is what
`Roster.size` returns) rather than `(sample s).card`; the two agree by
`Roster.card_toFinset`, which is a proof and so not stated here.

The order of lines inside `Program.step` (unconditional erase, pick, first
`cardEq`, thinning, halving, second `cardEq`, ⊥) is the transcript's
(esa22-final.tex:422-445); this file does not restate it — that is the bridge
in `Interface/ProgramModel.lean`.
-/

set_option autoImplicit false

namespace Esa22Copy.Interface

open Arlib.Computation

/-! ## 1. Class collapse -/

/-- A roster operation charges `StdOp.roster`. -/
@[simp] theorem rosterOps_charge (o : RosterOp) :
    (RosterOps.charge o : StdOp) = StdOp.roster o := rfl

/-- A randomness operation charges `StdOp.rand`. -/
@[simp] theorem randOps_charge (o : RandOp) :
    (RandOps.charge o : StdOp) = StdOp.rand o := rfl

/-- A register operation charges `StdOp.slot`. -/
@[simp] theorem slotOps_charge (o : SlotOp) :
    (SlotOps.charge o : StdOp) = StdOp.slot o := rfl

/-- Every element of a roster occupies the one `Cell`. -/
@[simp] theorem rosterCells_cell (ι : Type) :
    (RosterCells.cell ι : Cell) = Cell.cell := rfl

/-! ## 2. Views -/

section Views

variable {n : ℕ}

/-- The sample `X` held by a state.  **Specification-only.** -/
noncomputable def sample (s : Program.State n) : Finset (Fin n) := s.X.toFinset

/-- The level `k` of the sampling rate `p = 2⁻ᵏ` of a state.
**Specification-only.** -/
noncomputable def level (s : Program.State n) : ℕ := s.rate.levelOf

/-- Whether the run is still going: ⊥ has not been output.
**Specification-only.** -/
noncomputable def running (s : Program.State n) : Bool := s.bot.get.isNone

@[simp] theorem sample_init : sample (Program.init : Program.State n) = ∅ := rfl

@[simp] theorem level_init : level (Program.init : Program.State n) = 0 := rfl

@[simp] theorem running_init : running (Program.init : Program.State n) = true := rfl

end Views

/-- The outcome of a Bernoulli(`2⁻ᵏ`) pick read off a block of `L` fair bits: the
first `k` bits are all one (`false` when `k > L`). -/
noncomputable def pickAccepts {L : ℕ} (k : ℕ) (b : Block L) : Bool :=
  if k ≤ L then ((List.ofFn b.get).take k).all id else false

/-- What `Sampler.accept` returns, as `pickAccepts` at the sampler's level. -/
@[simp] theorem val_accept {κ κₛ : Type} [DecidableEq κ] [RandOps κ] {L : ℕ}
    (b : Block L) (r : Sampler) :
    (Sampler.accept b r : Charged κ κₛ Bool).val = pickAccepts r.levelOf b := rfl

/-! ## 3. Handles on the program -/

section Handles

variable {n L : ℕ}

/-- One iteration of the loop (lines 3-8), as a state transition. -/
noncomputable def stepState (thr : ℕ) (s : Program.State n) (ad : Fin n × Program.Draw n L) :
    Program.State n :=
  (Program.step thr s ad).val

/-- The loop run over the items-with-draws `l`, starting from `s`, as a state. -/
noncomputable def foldState (thr : ℕ) (l : List (Fin n × Program.Draw n L))
    (s : Program.State n) : Program.State n :=
  (Charged.foldl (Program.step thr) l s).val

@[simp] theorem foldState_nil (thr : ℕ) (s : Program.State n) :
    foldState (L := L) thr [] s = s := rfl

@[simp] theorem foldState_cons (thr : ℕ) (ad : Fin n × Program.Draw n L)
    (l : List (Fin n × Program.Draw n L)) (s : Program.State n) :
    foldState thr (ad :: l) s = foldState thr l (stepState thr s ad) := rfl

/-- The state after the loop of Algorithm 1 on `A`, reading draw `i` at item `i`. -/
noncomputable def finalState (thr : ℕ) (A : List (Fin n)) (tape : List (Program.Draw n L)) :
    Program.State n :=
  foldState thr (A.zip tape) Program.init

/-- Line 11: ⊥ if it was output, `|X| · 2ᵏ` otherwise. -/
noncomputable def answerOf (s : Program.State n) : Option ℕ :=
  if running s then some (s.X.card * 2 ^ level s) else none

end Handles

end Esa22Copy.Interface
