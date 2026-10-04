import Nfa.Model.Program
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Where the coins come from

`Nfa.Program.countNFA` reads its coins from a sealed `Tape`: one natural number per
coin site, turned into a Bernoulli(`p`) outcome by `Operations.bernoulliDigit`.
This file says how the tape is drawn — every listed site independently,
Geometric(1/2), `P(k) = 2^{-(k+1)}` — and so fixes the algorithm's law.

**Which sites are drawn, and why that is all of them.**  `sites A n P` lists every
`Site` a run with parameters `P` can read: core run `j < μ`, any state `q`,
repetition `r < α`, source `none` (line:final_reduce) or `some q'` (line:normalize),
and every word of length `1..n` — a coin of layer `i` decides a word of length
exactly `i`, and coins occur only in layers `1..n`.  A site off the list keeps the
deterministic draw `0`, so if the list missed a site the program reads, that coin
would silently stop being random; covering every read site is what the list is
for, and the analysis has to use it.  Distinct sites are distinct coins, and no
execution reads a site twice (see `Operations.Site`), so independent draws per
site are the paper's independent coins (algorithm.tex:52) and its independent core
runs (analysis.tex:63).
-/

set_option autoImplicit false

namespace Nfa.Run

open Nfa.Model.Operations

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- **One cell of randomness**: a Geometric(1/2) index, `P(k) = 2^{-(k+1)}`. -/
noncomputable def coinIndex : PMF ℕ :=
  (ProbabilityTheory.geometricMeasure ⟨2⁻¹, by norm_num, by norm_num⟩).toPMF

/-- All `2^ℓ` binary words of length `ℓ`. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | ℓ + 1 => (words ℓ).flatMap fun w => [w ++ [false], w ++ [true]]

/-- **Every coin site a run of `countNFA A σ n P _` can read** (see the module
docstring). -/
noncomputable def sites (n : ℕ) (P : Params) : List (Site Q) :=
  let states : List Q := (Finset.univ : Finset Q).toList
  (List.range P.μ).flatMap fun j => states.flatMap fun q =>
    (List.range P.α).flatMap fun r => (none :: states.map some).flatMap fun src =>
      (List.range' 1 n).flatMap fun ℓ => (words ℓ).map fun u => ⟨j, q, r, src, u⟩

/-- **The tape**: an independent `coinIndex` at every listed site, `0` elsewhere.
Written by recursion so that the cons case unfolds definitionally. -/
noncomputable def tapeLaw : List (Site Q) → PMF (Site Q → ℕ)
  | [] => PMF.pure fun _ => 0
  | s :: ss => coinIndex.bind fun k => (tapeLaw ss).map fun f => Function.update f s k

/-- **The algorithm, as a distribution over charged computations**: `countNFA` run
with the paper's parameters `params A n ε δ` on a tape drawn from `tapeLaw`.  Its
value is what the algorithm returns and its tally is what that execution cost. -/
noncomputable def run (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (ε δ : ℝ) :
    PMF (Arlib.Computation.Charged Op Cell Scalar) :=
  (tapeLaw (sites n (params A n ε δ))).map fun f =>
    Nfa.Program.countNFA A σ n (params A n ε δ) (Tape.ofFun f)

/-- **The output distribution**: the law of the returned estimate `est`, read as a
real number. -/
noncomputable def output (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (ε δ : ℝ) : PMF ℝ :=
  (run A σ n ε δ).map fun c => ((c.val.get : ℚ) : ℝ)

end Nfa.Run

#modelClosure Nfa.Run.run
#modelClosure Nfa.Run.output
