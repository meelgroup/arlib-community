import Nfa.Model.Run

/-!
# Encoding: what the specification reads off a run of `countNFA`

Nothing here is a claim.  Every lemma is `rfl`; every definition is a
noncomputable *view* of something `Nfa.Model.Program` or `Nfa.Model.Run` already
holds, or a name for a subterm of a `Model/` definition.  The bridge that proves
the program's output law equal to the pseudocode's is `Interface/ProgramModel.lean`;
the pseudocode itself is `Interface/Pseudocode.lean`.  No headline statement
mentions anything declared here.

## 1. The class indirection

The program is charged in the project currency `Nfa.Model.Operations.Op`, which
names arlib's dictionary operations through the instance `instRosterOps` of
`Arlib.Computation.RosterOps`; the cache's row index is a `Roster (List Bool)`
whose cells are arlib's `Cell` through the low-priority `stdRosterCells`.  A tally
produced by `Roster.mem` says `Roster.opcode Op .mem`, a statement about `rate`
says `Op.rosterMem`: definitionally equal, syntactically not, and `simp` stops at
`CostVec.one (Roster.opcode Op .mem)`.  One lemma for the class collapses it:

* `rosterOpcode` — `Roster.opcode Op o` (`RosterOps.charge o`) is the constructor
  of `Op` the instance names.

The other class the program goes through, `RosterCells (List Bool) Cell`, gets no
lemma: `simp` already closes `Roster.cell (List Bool) = Cell.cell` unaided, and no
space claim is made.  `Operations.Cell` is an `abbrev` of `Arlib.Computation.Cell`,
so it is reducible and needs no lemma either.

## 2. Views of a run

The run's numbers live in the sealed register `Operations.Scalar` (view `Scalar.get`,
rational) and its sample sets in arrays of duplicate-free lists.  The analysis is
over reals and `Finset`s:

| paper | program holds | view |
|---|---|---|
| a number `p(q)`, `ρ(q)`, `Y_{q,b}`, `est_j` | `Scalar` | `real` |
| `S^r(q)` | `Samples` (`Array (List (List Bool))`) at index `r` | `sampleSet` |
| `p(q^i)`, `S^r(q^i)` of the layer in progress | `CoreState.curP`, `.curS` | `CoreState` views `curPReal`, `curSet` |
| `p(q^{i-1})`, `S^r(q^{i-1})` | `CoreState.prevP`, `.prevS` | `prevPReal`, `prevSet` |
| `Σ_{r,q} |S^r(q)|` (line:interrupt) | `CoreState.total` | `totalReal` |
| rows of `cache_{i-1}` | `CoreState.cache` | `cacheRows` (arlib's `Roster.toFinset`) |
| the returned `est` | `Charged Op Cell Scalar` | `answer` |

The values of the primitives of `Nfa.Model.Operations`, read through these views,
are recorded as `rfl` lemmas (`get_val_lit`, …, `val_coin_ofFun`), because the
registers' contents are private and a proof cannot otherwise write them down.
The value of `isWitness` is not among them: it branches on a stuck Boolean and is
not `rfl`, so it is a claim for `ProgramModel`.

## 3. Handles on `Model/` subterms

* `execution A σ n ε δ f` — the charged computation `Run.run` maps the drawn tape
  `f` to: `countNFA A σ n (params A n ε δ) (Tape.ofFun f)`;
* `run_eq` — `Run.run` is `tapeLaw (sites …)` pushed through `execution`;
* `output_eq` — `Run.output` is `Run.run` pushed through `answer`.

## Correspondence with the restatement's `algorithmTranscript`

Pseudocode-side transcriptions are `Interface/Pseudocode.lean`'s business; this
file only fixes how the program's carriers are read.  Each step of the transcript
is located in `Nfa.Model.Program` by that file's correspondence ledger; the views
above are the reads those steps need:

* countNFA.4/.6 (line:p_q_init, line:S_q_init) — `curPReal`, `curSet` of the
  initial `CoreState`;
* countNFA.11 (line:interrupt) — `totalReal` against `real` of `θ`;
* countNFA.12 (updateCache) — `cacheRows`;
* countNFA.13/.14 — `answer`;
* eAS.1–eAS.8 — `prevPReal`, `prevSet` (inputs) and `curPReal`, `curSet`
  (outputs) of one `estimateAndSample` call;
* reduce — `val_coin_ofFun`: one coin reads the tape's draw at its site.

No transcript step is missing from `Model/Program.lean`; the only departures it
records are the ones its own ledger states (in-layer `≺`-order, order-statistic
median, `hat ρ = +∞` branch, `0` on an empty slice, selector `σ` for eq. union).
-/

set_option autoImplicit false

namespace Nfa.Interface

open Arlib.Computation (Charged Roster RosterOp)
open Nfa.Model.Operations

/-! ## 1. The class indirection -/

/-- **The dictionary opcodes of the project currency**, one lemma for the class:
the opcode `RosterOps` assigns a standard roster operation is the matching
constructor of `Op`. -/
@[simp] theorem rosterOpcode (o : RosterOp) :
    Roster.opcode Op o =
      match o with
      | .erase => Op.rosterErase
      | .insert => Op.rosterInsert
      | .size => Op.rosterSize
      | .cardEq => Op.rosterCardEq
      | .mem => Op.rosterMem := rfl

/-! ## 2. Views of a run -/

section Views

variable {Q : Type}

/-- **The real number a sealed register holds.** -/
noncomputable def real (x : Scalar) : ℝ := ((x.get : ℚ) : ℝ)

/-- **`S^r(q)` as a set**: the `r`-th sample set of one state.  An index past the
end reads as `∅`, as the program's `getD r []` does. -/
noncomputable def sampleSet (S : Nfa.Program.Samples) (r : ℕ) : Finset (List Bool) :=
  (S.getD r []).toFinset

/-- `p(q^i)` for the layer in progress (`1` until `q` is processed). -/
noncomputable def curPReal (s : Nfa.Program.CoreState Q) (q : Q) : ℝ := real (s.curP q)

/-- `S^r(q^i)` for the layer in progress (`∅` until `q` is processed). -/
noncomputable def curSet (s : Nfa.Program.CoreState Q) (q : Q) (r : ℕ) :
    Finset (List Bool) :=
  sampleSet (s.curS q) r

/-- `p(q^{i-1})` for the previous layer. -/
noncomputable def prevPReal (s : Nfa.Program.CoreState Q) (q : Q) : ℝ := real (s.prevP q)

/-- `S^r(q^{i-1})` for the previous layer. -/
noncomputable def prevSet (s : Nfa.Program.CoreState Q) (q : Q) (r : ℕ) :
    Finset (List Bool) :=
  sampleSet (s.prevS q) r

/-- The stored-sample count line:interrupt compares against `θ`. -/
noncomputable def totalReal (s : Nfa.Program.CoreState Q) : ℝ := real s.total

/-- The words indexing the rows of `cache_{i-1}`. -/
noncomputable def cacheRows (s : Nfa.Program.CoreState Q) : Finset (List Bool) :=
  s.cache.toFinset

/-- **The returned estimate `est`** of one execution, as a real number. -/
noncomputable def answer (c : Charged Op Cell Scalar) : ℝ := real c.val

end Views

/-! ### The primitives' values, through the views -/

section Values

variable {Q : Type}

@[simp] theorem get_val_lit (a : ℚ) : (Scalar.lit a).val.get = a := rfl

@[simp] theorem get_val_add (x y : Scalar) : (Scalar.add x y).val.get = x.get + y.get := rfl

@[simp] theorem get_val_mul (x y : Scalar) : (Scalar.mul x y).val.get = x.get * y.get := rfl

@[simp] theorem get_val_div (x y : Scalar) : (Scalar.div x y).val.get = x.get / y.get := rfl

@[simp] theorem get_val_min (x y : Scalar) :
    (Scalar.min x y).val.get = min x.get y.get := rfl

@[simp] theorem val_le (x y : Scalar) : (Scalar.le x y).val = decide (x.get ≤ y.get) := rfl

/-- The median the program returns: the `⌊k/2⌋`-th smallest entry, `0` for `[]`.
That this is arlib's `medianOf` of the same entries is a claim, not stated here. -/
@[simp] theorem get_val_median (xs : List Scalar) :
    (Scalar.median xs).val.get =
      ((xs.map Scalar.get).mergeSort (fun a b => decide (a ≤ b))).getD (xs.length / 2) 0 :=
  rfl

/-- **One coin of `reduce`** reads the drawn tape at its own site. -/
@[simp] theorem val_coin_ofFun (site : Site Q) (p : Scalar) (f : Site Q → ℕ) :
    (coin site p (Tape.ofFun f)).val = bernoulliDigit (f site) p.get := rfl

@[simp] theorem val_transition (A : PaperNFA Q) (q' : Q) (b : Bool) (q : Q) :
    (transition A q' b q).val = A.delta q' b q := rfl

@[simp] theorem val_sameState [DecidableEq Q] (q q' : Q) :
    (sameState q q').val = decide (q = q') := rfl

@[simp] theorem val_extend (w : List Bool) (b : Bool) : (extend w b).val = w ++ [b] := rfl

@[simp] theorem val_addWord (u : List Bool) (T : List (List Bool)) :
    (addWord u T).val = u :: T := rfl

@[simp] theorem get_val_size (T : List (List Bool)) : (size T).val.get = T.length := rfl

@[simp] theorem val_ceilDiv (a b : ℕ) : (ceilDiv a b).val = (a + b - 1) / b := rfl

end Values

/-! ## 3. Handles on `Model/` subterms -/

section Handles

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- **The execution on a drawn tape**: the charged computation `Run.run` maps the
draws `f` to, with the paper's parameters. -/
noncomputable def execution (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (ε δ : ℝ)
    (f : Site Q → ℕ) : Charged Op Cell Scalar :=
  Nfa.Program.countNFA A σ n (params A n ε δ) (Tape.ofFun f)

theorem run_eq (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (ε δ : ℝ) :
    Run.run A σ n ε δ =
      (Run.tapeLaw (Run.sites n (params A n ε δ))).map (execution A σ n ε δ) := rfl

theorem output_eq (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (ε δ : ℝ) :
    Run.output A σ n ε δ = (Run.run A σ n ε δ).map answer := rfl

end Handles

end Nfa.Interface
