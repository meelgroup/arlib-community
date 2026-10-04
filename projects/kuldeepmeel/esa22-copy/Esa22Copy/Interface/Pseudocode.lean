import Esa22Copy.Model.Prelude
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Powerset

/-!
# Pseudocode: Algorithm 1 (F0-Estimator) as mathematics

Algorithm 1 of esa22-final.tex:422-445, written over `Finset`, `ℕ` and `PMF`
for the correctness proof.  The object transported to the headline is the law
of the **answer**, `outputLaw A ε δ : PMF (Option ℕ)` (`none` = ⊥,
`some (|X|·2ᵏ)` = `|X|/p`); the bridge (`Interface/ProgramModel.lean`, next
pass) is to identify it with `Esa22Copy.output A ε δ`.  Space is not modelled
here: it is an operator on the charged program `Esa22Copy.Program.estimator`
and stays there.

## Why there are two definitions of the same algorithm

`Model/Program.lean` and this file describe one algorithm, and neither is dead
weight.  It is not about computability — everything here is noncomputable, and
so is every view of the program's carriers.  It is that **a sealed dictionary is
not extensional**.  The program's sample is an `Arlib.Computation.Roster`: an
ordered, duplicate-free list, because the algorithm's expensive operation (the
thinning pass of line 6) *is* an iteration over it, and that iteration is what
the cost model has to charge correctly.  Two rosters holding the same set by
different insertion histories are different terms.  The correctness argument —
Claim lm:fail, the agreement with Algorithm 2 off ⊥, the coupling with
Algorithm 3's `Y_{k,j}` — compares laws of *sets*.  `Finset` is exactly the
quotient that argument needs, and a law over states whose sample is a `Finset`
is what Mathlib's `PMF` lemmas apply to.

## Correspondence ledger

Paper step (algorithmTranscript), the declaration here, and the program
declaration the bridge is to match it with.

| paper (Algorithm 1) | pseudocode | program (`Esa22Copy.Program`) |
|---|---|---|
| Input `A, ε, δ`; `m = A.length` | `outputLaw A ε δ` | `estimator thr A tape` (via `Esa22Copy.run`) |
| line 1: `p ← 1; X ← ∅` | `init` | `init` |
| line 1: `thresh ← ⌈(12/ε²) log(8m/δ)⌉` | argument `thr`, set to `thresh ε δ A.length` in `outputLaw` | argument `thr`, set in `Esa22Copy.run` |
| line 2: `for i = 1 to m` | `loop` | `Charged.foldl (step thr) (A.zip tape) init` |
| (halt after ⊥) | `step` tests `running` and is `PMF.pure s` once ⊥ | `step` tests `Slot.isEmpty` and is `pure s` |
| line 3: `X ← X \ {aᵢ}` | `drop` | `Roster.erase` |
| line 4: w.p. `p`, `X ← X ∪ {aᵢ}` | `pick` (with `firstOnes`) | `Sampler.accept d.pick`, `Roster.insert` |
| line 5: `if \|X\| = thresh` | `full` | first `Roster.cardEq thr` |
| line 6: throw away each element w.p. ½ | `throw` | `Roster.filterErase (Coins.flip · d.thin)` |
| line 7: `p ← p/2` | `halve` | `Sampler.halve` |
| line 8: `if \|X\| = thresh` Output ⊥ | `check` | second `Roster.cardEq thr`, `Slot.fill ()` |
| line 11: Output `\|X\|/p` | `answer` (and `rate`, `answer_cast`) | `Slot.isEmpty`, `Roster.size`, `Sampler.inflate` |

No `MODEL:` gap was found: `Model/Program.lean` performs every step of the
transcript in the transcript's order (unconditional erase, pick, first size
test, thinning, halving, second size test and ⊥), freezes the state after ⊥,
and reads fresh, separate coins for the pick and the thinning.

## Decisions made here

* **The model does what the program can do, no more.**  The level `k` of
  `p = 2⁻ᵏ` is held as a `ℕ` and only ever used the way `Sampler.accept`,
  `Sampler.halve` and `Sampler.inflate` use it; the ⊥ register is a `Bool` that
  is only tested.  After ⊥ the state is frozen, as in the program — it is not
  replaced by a separate "⊥" constructor, so the abstraction of a program state
  is just its three views (`Interface.sample`, `Interface.level`,
  `Interface.running`).
* **The pick is drawn against `L` fair bits**, exactly as `Model/Run.lean`
  draws it: uniform `Fin L → Bool`, accepted iff the first `k` bits are all one
  (`firstOnes`, which is `false` when `k > L`, as `Sampler.accept` is).  That is
  Bernoulli(`2⁻ᵏ`) only when `k ≤ L`; with `L = A.length + 1` it holds on every
  reachable state, and showing so is the analysis's business — not a hypothesis
  here, since a hypothesis here would be a case split in every bridge lemma.
* **Coins are drawn lazily.**  The program reads one pick block and one
  thinning `Coins` per item from a tape drawn up front, and reads the coins only
  when it thins; here the pick bits are drawn inside `pick`, the thinning coins
  (a uniform subset of `Fin n` = one fair coin per element, heads keeps) only
  inside `throw`, and nothing is drawn after ⊥.  Unread draws do not change the
  law, so these are the same distribution.
* **No resource fields.**  Nothing here counts operations or cells.
* **Not here:** Algorithm 2 (no ⊥ check), Algorithm 3 (`Y_{k,j}`), and every
  event of the analysis; those are added by the passes that use them.
-/

set_option autoImplicit false

noncomputable section

namespace Esa22Copy.Interface.Pseudocode

/-- **The state of Algorithm 1**: the sample `X`, the level `k` of the sampling
rate `p = 2⁻ᵏ`, and whether the run is still going (⊥ not yet output). -/
structure State (n : ℕ) where
  /-- The sample set `X`. -/
  X : Finset (Fin n)
  /-- The level `k` of the rate: `p = 2⁻ᵏ`. -/
  level : ℕ
  /-- `true` until ⊥ is output (line 8); a run that has output ⊥ has halted. -/
  running : Bool

variable {n : ℕ}

/-- The sampling rate `p = 2⁻ᵏ` of a state, as the paper writes it. -/
def rate (s : State n) : ℝ := (2⁻¹ : ℝ) ^ s.level

/-- Line 1: `p ← 1`, `X ← ∅`, nothing output yet. -/
def init : State n := ⟨∅, 0, true⟩

/-- Line 3: `X ← X \ {aᵢ}`, unconditionally (a no-op when `aᵢ ∉ X`). -/
def drop (a : Fin n) (s : State n) : State n := { s with X := s.X.erase a }

/-- The outcome of the pick read off `L` fair bits at level `k`: the first `k`
bits are all one, and `false` when `k > L` (as `Sampler.accept` decides it). -/
def firstOnes {L : ℕ} (k : ℕ) (bits : Fin L → Bool) : Bool :=
  if k ≤ L then ((List.ofFn bits).take k).all id else false

/-- Line 4: with probability `p = 2⁻ᵏ`, `X ← X ∪ {aᵢ}` — a fresh block of `L`
fair bits, accepted iff its first `k` bits are all one. -/
def pick (L : ℕ) (a : Fin n) (s : State n) : PMF (State n) :=
  (PMF.uniformOfFintype (Fin L → Bool)).map fun bits =>
    if firstOnes s.level bits then { s with X := insert a s.X } else s

/-- Line 5: the test `|X| = thresh`. -/
def full (thr : ℕ) (s : State n) : Bool := decide (s.X.card = thr)

/-- Line 6: throw away each element of `X` with probability ½ — one fresh fair
coin per element (a uniform subset of `Fin n` is the set of heads), keeping the
heads. -/
def throw (s : State n) : PMF (State n) :=
  (PMF.uniformOfFintype (Finset (Fin n))).map fun heads =>
    { s with X := s.X.filter (· ∈ heads) }

/-- Line 7: `p ← p/2`, i.e. `k ← k + 1`. -/
def halve (s : State n) : State n := { s with level := s.level + 1 }

/-- Line 8: if `|X| = thresh` still, output ⊥ (and halt). -/
def check (thr : ℕ) (s : State n) : State n :=
  if full thr s then { s with running := false } else s

/-- One iteration of the loop, lines 3-8, on item `a`.  A run that has output ⊥
is left as it is. -/
def step (L thr : ℕ) (s : State n) (a : Fin n) : PMF (State n) :=
  if s.running then
    (pick L a (drop a s)).bind fun s =>
      if full thr s then (throw s).map fun s => check thr (halve s)
      else PMF.pure s
  else PMF.pure s

/-- Line 2: the loop over the items of `A`, from state `s`. -/
def loop (L thr : ℕ) : List (Fin n) → State n → PMF (State n)
  | [], s => PMF.pure s
  | a :: A, s => (step L thr s a).bind (loop L thr A)

/-- Line 11: ⊥ if it was output, otherwise the estimate `|X|/p = |X|·2ᵏ`. -/
def answer (s : State n) : Option ℕ :=
  if s.running then some (s.X.card * 2 ^ s.level) else none

/-- The law of the state after the loop, with pick blocks of `L` bits and
threshold `thr`. -/
def stateLaw (L thr : ℕ) (A : List (Fin n)) : PMF (State n) := loop L thr A init

/-- The law of the answer, with pick blocks of `L` bits and threshold `thr`. -/
def answerLaw (L thr : ℕ) (A : List (Fin n)) : PMF (Option ℕ) :=
  (stateLaw L thr A).map answer

/-- **What Algorithm 1 returns on `(A, ε, δ)`**: threshold `thresh ε δ A.length`
and pick blocks of `A.length + 1` bits, as `Esa22Copy.run` instantiates them. -/
def outputLaw (A : List (Fin n)) (ε δ : ℝ) : PMF (Option ℕ) :=
  answerLaw (A.length + 1) (thresh ε δ A.length) A

/-- The integer the algorithm returns is the paper's real `|X|/p`, for
`p = 2⁻ᵏ`. -/
theorem answer_cast (s : State n) :
    ((s.X.card * 2 ^ s.level : ℕ) : ℝ) = (s.X.card : ℝ) / rate s := by
  rw [rate, inv_pow, div_inv_eq_mul]
  push_cast
  rfl

end Esa22Copy.Interface.Pseudocode

end
