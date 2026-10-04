import Esa22Copy.Model.Prelude
import Esa22Copy.Model.Program
import Esa22Copy.Meta.ModelClosure
import Arlib.Computation.ChargedPMF
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Powerset

/-!
# Run: where Algorithm 1's coins come from

`Esa22Copy.Program.estimator` takes its randomness as an argument and computes.
This file says how that argument is drawn, and nothing else.

* `drawLaw n L` — one iteration's randomness: a uniform block of `L` fair bits
  for the pick (line 4), and, **independently**, a uniform subset of `Fin n` as
  the thinning coins (line 6) — a uniform subset is exactly one independent fair
  coin per element.
* `tapeLaw n L k` — `k` independent draws, written by recursion so the
  successor case unfolds definitionally to "one fresh draw, then the rest".
* `run A ε δ` — the law of the charged execution of Algorithm 1 on `A`, with the
  threshold instantiated at exactly `thresh ε δ A.length`.  Accuracy is read off
  `output`; worst-case space is read off this same object by `worstSpace`.
* `output A ε δ` — the law of what the algorithm returns (`none` = ⊥).

## Decisions made here

* **Tape length = `A.length`.**  The program pairs item `i` with draw `i` by
  `A.zip tape`; a shorter tape would silently truncate the run and a longer one
  would leave draws unread.  Drawing exactly `A.length` cells makes the pairing
  total: every item gets its own fresh draw.
* **Block length = `A.length + 1`** (as in Algorithm 3, esa22-final.tex:589).
  `Sampler.accept` at level `k` on a block of length `L` is Bernoulli(`2⁻ᵏ`) only
  when `k ≤ L` (it returns `false` otherwise).  The level rises at most once per
  item, so before item `i` it is at most `i - 1 < A.length + 1`; the block is long
  enough on every reachable state.  (Proof obligation for `Analysis/`.)
* **Fresh, independent coins per iteration.**  Each cell is drawn independently
  of the others, and inside a cell the pick bits and the thinning coins are
  drawn independently.  Thinning coins are drawn every iteration and read only
  when thinning happens; unread coins do not change the law of the run.
* **No `Nonempty (Fin n)` is needed**: the uniform laws are over `Fin L → Bool`
  and `Finset (Fin n)`, both nonempty for every `n`, so the headline covers
  `n = 0` (which forces `A = []`).
-/

set_option autoImplicit false

noncomputable section

namespace Esa22Copy

open Arlib.Computation
open Esa22Copy.Model

/-- **One iteration's randomness**: `L` fair bits for the pick and, independently,
one fair coin per element of `Fin n` for the thinning pass. -/
def drawLaw (n L : ℕ) : PMF (Program.Draw n L) :=
  (PMF.uniformOfFintype (Fin L → Bool)).bind fun bits =>
    (PMF.uniformOfFintype (Finset (Fin n))).bind fun heads =>
      PMF.pure ⟨Block.ofFun bits, Coins.ofFinset heads⟩

/-- **The tape**: `k` independent draws of `drawLaw n L`. -/
def tapeLaw (n L : ℕ) : ℕ → PMF (List (Program.Draw n L))
  | 0 => PMF.pure []
  | k + 1 => (drawLaw n L).bind fun d => (tapeLaw n L k).map fun t => d :: t

/-- **Algorithm 1 run on `A` with parameters `ε, δ`**, as a distribution over
charged executions: threshold `thresh ε δ A.length`, one fresh draw per item,
pick blocks of length `A.length + 1`. -/
def run {n : ℕ} (A : List (Fin n)) (ε δ : ℝ) :
    PMF (Charged Operations.Op Operations.Cell (Option ℕ)) :=
  (tapeLaw n (A.length + 1) A.length).map
    (Program.estimator (thresh ε δ A.length) A)

/-- **What Algorithm 1 returns**: `none` for ⊥, `some (|X|·2ᵏ)` otherwise. -/
def output {n : ℕ} (A : List (Fin n)) (ε δ : ℝ) : PMF (Option ℕ) :=
  (run A ε δ).map Charged.val

end Esa22Copy

end

#modelClosure Esa22Copy.drawLaw
#modelClosure Esa22Copy.tapeLaw
#modelClosure Esa22Copy.run
#modelClosure Esa22Copy.output
