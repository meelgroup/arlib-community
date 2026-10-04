import Esa22Copy.Interface.Pseudocode

/-!
# Algorithm 2 and Algorithm 3's `Y_k` process

Two auxiliary algorithms of the paper's proof of Claim claim:errfail, as `PMF`s
over the pseudocode's state type.

* `step2` / `loop2` — **Algorithm 2** (esa22-final.tex:545-567): Algorithm 1 with
  the ⊥ test of line 8 removed.  The `running` flag is never touched.
* `yStep` / `yRun` / `yLaw` — **Algorithm 3's set `Y_k`** for one fixed `k`
  (esa22-final.tex:569-606): on each arrival `aᵢ`, drop `aᵢ` and re-add it
  with probability `2^{-k}` (`k ≤ FirstZeroIndex(r)`), with a fresh coin.
  Only one `k` at a time is ever needed, so the joint construction over all
  `k` (one bit string per arrival) is not built: the analysis uses `Y_k`'s
  law, never a pointwise coupling.

`loop2_append` / `yRun_append` expose the last step, since the analysis argues
from the end of the stream.
-/

set_option autoImplicit false

noncomputable section

namespace Esa22Copy.Analysis.Alg2

open Esa22Copy.Interface.Pseudocode

variable {n : ℕ}

/-- One iteration of **Algorithm 2** (lines 3-7 of Algorithm 1, no ⊥ test).
PAPER: esa22-final.tex:552-564 -/
def step2 (L thr : ℕ) (s : State n) (a : Fin n) : PMF (State n) :=
  (pick L a (drop a s)).bind fun s =>
    if full thr s then (throw s).map halve else PMF.pure s

/-- **Algorithm 2**'s loop over the items of a stream, from state `s`.
PAPER: esa22-final.tex:552-566 -/
def loop2 (L thr : ℕ) : List (Fin n) → State n → PMF (State n)
  | [], s => PMF.pure s
  | a :: A, s => (step2 L thr s a).bind (loop2 L thr A)

/-- The keep probability `2^{-k}` as an `ℝ≥0` at most one.
INTERNAL: packaging for `PMF.bernoulli`. -/
def keepProb (k : ℕ) : NNReal := (2⁻¹ : NNReal) ^ k

/-- `2^{-k} ≤ 1`.
INTERNAL: side condition of `PMF.bernoulli`. -/
theorem keepProb_le_one (k : ℕ) : keepProb k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

/-- One arrival in **Algorithm 3**, for one `k`: `Y_k ← Y_k \ {a}`, then
`Y_k ← Y_k ∪ {a}` with probability `2^{-k}` (a fresh coin).
PAPER: esa22-final.tex:597-602 -/
def yStep (k : ℕ) (a : Fin n) (Y : Finset (Fin n)) : PMF (Finset (Fin n)) :=
  (PMF.bernoulli (keepProb k) (keepProb_le_one k)).map fun c =>
    if c then insert a (Y.erase a) else Y.erase a

/-- **Algorithm 3**'s `Y_k` after the items of a stream, from `Y`.
PAPER: esa22-final.tex:595-604 -/
def yRun (k : ℕ) : List (Fin n) → Finset (Fin n) → PMF (Finset (Fin n))
  | [], Y => PMF.pure Y
  | a :: A, Y => (yStep k a Y).bind (yRun k A)

/-- The law of `Y_{k,m}` on the stream `A`, i.e. `Y_k` started empty.
PAPER: esa22-final.tex:677 -/
def yLaw (k : ℕ) (A : List (Fin n)) : PMF (Finset (Fin n)) := yRun k A ∅

/-- Algorithm 2 on `A ++ [a]` is Algorithm 2 on `A` followed by one step on `a`.
INTERNAL: exposes the last iteration for induction from the end of the stream. -/
theorem loop2_append (L thr : ℕ) (A : List (Fin n)) (a : Fin n) (s : State n) :
    loop2 L thr (A ++ [a]) s = (loop2 L thr A s).bind fun t => step2 L thr t a := by
  induction A generalizing s with
  | nil => simp [loop2, PMF.pure_bind, PMF.bind_pure]
  | cons b A ih =>
    simp only [List.cons_append, loop2, PMF.bind_bind]
    exact congrArg _ (funext ih)

/-- `Y_k` on `A ++ [a]` is `Y_k` on `A` followed by one arrival of `a`.
INTERNAL: exposes the last arrival for induction from the end of the stream. -/
theorem yRun_append (k : ℕ) (A : List (Fin n)) (a : Fin n) (Y : Finset (Fin n)) :
    yRun k (A ++ [a]) Y = (yRun k A Y).bind fun Z => yStep k a Z := by
  induction A generalizing Y with
  | nil => simp [yRun, PMF.pure_bind, PMF.bind_pure]
  | cons b A ih =>
    simp only [List.cons_append, yRun, PMF.bind_bind]
    exact congrArg _ (funext ih)

end Esa22Copy.Analysis.Alg2

end
