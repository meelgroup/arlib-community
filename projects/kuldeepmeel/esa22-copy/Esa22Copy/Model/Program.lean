import Esa22Copy.Model.Operations
import Esa22Copy.Meta.CostSeal
import Esa22Copy.Meta.ModelClosure
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot

/-!
# Program: Algorithm 1 (F0-Estimator), as a charged computation

The algorithm of esa22-final.tex:422-445, transcribed line by line as a term of
`Charged Op Cell (Option ℕ)` over arlib's sealed carriers.  It takes the
threshold as a plain `ℕ` (the caller supplies `thresh ε δ A.length`) and the
randomness as a separate argument, a tape with one `Draw` per stream item.

## Encoding

* **State** — `X` is a `Roster (Fin n)` (the sample set), `p = 2⁻ᵏ` is a
  `Sampler` (its level `k` never leaves it), and the ⊥ register is a
  `Slot Unit`: filled exactly when the run has output ⊥.
* **Randomness** — iteration `i` reads its own `Draw`: a `Block L` of fair bits
  for the pick (`Sampler.accept` accepts iff the first `k` bits are all one, a
  Bernoulli(`2⁻ᵏ`) event when `k ≤ L`) and a `Coins (Fin n)` for the thinning
  pass (one fair coin per element, heads = keep).  The two are distinct fields,
  so thinning never reuses pick bits: this is Algorithm 1's randomness, not
  Algorithm 3's bit-reuse coupling, which is an analysis device only.
* **Output** — `none` is ⊥; `some (|X| · 2ᵏ)` is `|X|/p` (an integer, since `p`
  is dyadic).

**Why this encoding.**  It is the paper's own: a set, a dyadic rate, and fresh
coins per step.  The argument it leaves to `Analysis/` is the paper's: the ⊥
union bound over iterations (Claim lm:fail), agreement with Algorithm 2 off ⊥
(Claim claim:errfail), and the in-law coupling of Algorithm 2 with Algorithm 3's
`Y_{k,j}` (esa22-final.tex:678, asserted without proof in the paper — here it is
a proof obligation about the tape law in `Model/Run.lean`, not an assumption).

## Correspondence ledger

| paper (Algorithm 1) | Lean |
|---|---|
| Input `A`, `ε`, `δ` | `estimator thr A tape`; `ε, δ` enter only through `thr` |
| line 1: `p ← 1; X ← ∅` | `init` (`Sampler.start`, `Roster.empty`, `Slot.empty`) |
| line 1: `thresh ← ⌈(12/ε²) log(8m/δ)⌉` | argument `thr : ℕ` (noncomputable; see `Model/Prelude.lean`) |
| line 2: `for i = 1 to m` | `Charged.foldl (step thr) (A.zip tape) init` |
| line 3: `X ← X \ {aᵢ}` (unconditional) | `Roster.erase` in `step` |
| line 4: with probability `p`, `X ← X ∪ {aᵢ}` | `Sampler.accept d.pick`, then `Roster.insert` |
| line 5: `if \|X\| = thresh` | first `Roster.cardEq thr` in `step` |
| line 6: throw away each element w.p. ½ | `Roster.filterErase (Coins.flip · d.thin)` |
| line 7: `p ← p/2` | `Sampler.halve` |
| line 8: `if \|X\| = thresh` Output ⊥ | second `Roster.cardEq thr`, then `Slot.fill ()` |
| line 11: Output `\|X\|/p` | `Slot.isEmpty`, `Roster.size`, `Sampler.inflate` in `estimator` |

Represented differently (modelling notes, not omissions):

* **Halting on ⊥.**  The paper's `Output ⊥` stops the run.  Here the loop keeps
  folding but `step` first asks the register (`Slot.isEmpty`) and is `pure s` —
  no erase, pick or insert — once ⊥ is recorded, so the state is frozen by
  definition.  This adds one register test per remaining item to the tally
  (the paper claims no time bound) and no cells.
* **Tape length.**  `A.zip tape` pairs item `i` with draw `i`; `Model/Run.lean`
  draws a tape of length exactly `A.length`, so nothing is truncated.
* **Block length `L`.**  Generic here; `Model/Run.lean` fixes `L = A.length + 1`,
  which exceeds every reachable level (the level rises at most once per item).
-/

set_option autoImplicit false

namespace Esa22Copy.Program

open Arlib.Computation
open Esa22Copy.Model

/-- The randomness one iteration of the loop reads: a block of fair bits for the
pick (line 4) and one fair coin per element for the thinning pass (line 6). -/
structure Draw (n L : ℕ) where
  /-- The bits the Bernoulli(`p`) pick of line 4 is drawn against. -/
  pick : Block L
  /-- The coins of the thinning pass of line 6; heads keeps the element. -/
  thin : Coins (Fin n)

/-- The algorithm's state: the sample `X`, the rate `p = 2⁻ᵏ`, and the ⊥
register (filled once ⊥ has been output). -/
structure State (n : ℕ) where
  /-- The sample set `X`. -/
  X : Roster (Fin n)
  /-- The sampling rate `p`. -/
  rate : Sampler
  /-- Filled exactly when the run has output ⊥. -/
  bot : Slot Unit

/-- Line 1: `p ← 1`, `X ← ∅`, nothing output yet. -/
def init {n : ℕ} : State n := ⟨Roster.empty, Sampler.start, Slot.empty⟩

/-- One iteration of the loop (lines 3-8) on stream item `a` with its draw `d`.
A run that has already output ⊥ is left unchanged. -/
def step {n L : ℕ} (thr : ℕ) (s : State n) (ad : Fin n × Draw n L) :
    Charged Operations.Op Operations.Cell (State n) := do
  let (a, d) := ad
  let running ← Slot.isEmpty s.bot
  if running then
    -- line 3
    let X ← Roster.erase a s.X
    -- line 4
    let picked ← Sampler.accept d.pick s.rate
    let X ← if picked then Roster.insert a X else pure X
    -- line 5
    let full ← Roster.cardEq thr X
    if full then
      -- line 6
      let X ← Roster.filterErase (fun y => Coins.flip y d.thin) X
      -- line 7
      let rate ← Sampler.halve s.rate
      -- line 8
      let stuck ← Roster.cardEq thr X
      if stuck then
        let bot ← Slot.fill () s.bot
        pure ⟨X, rate, bot⟩
      else
        pure ⟨X, rate, s.bot⟩
    else
      pure ⟨X, s.rate, s.bot⟩
  else
    pure s

/-- **Algorithm 1, F0-Estimator**, run with threshold `thr` on stream `A`,
reading draw `i` of `tape` at item `i`.  Returns `none` for ⊥ and
`some (|X| · 2ᵏ)` (that is, `|X|/p`) otherwise. -/
def estimator {n L : ℕ} (thr : ℕ) (A : List (Fin n)) (tape : List (Draw n L)) :
    Charged Operations.Op Operations.Cell (Option ℕ) := do
  -- lines 1-10
  let s ← Charged.foldl (step thr) (A.zip tape) init
  -- line 11
  let notBot ← Slot.isEmpty s.bot
  if notBot then
    let size ← Roster.size s.X
    let est ← Sampler.inflate size s.rate
    pure (some est)
  else
    pure none

end Esa22Copy.Program

#programSeal Esa22Copy.Program
#executableModule Esa22Copy.Model.Program
#surplusIn Esa22Copy.Model.Program from Esa22Copy.Program.estimator
