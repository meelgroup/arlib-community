import Nfa.Interface.Pseudocode

/-!
# `countNFAcore*`: the core run without line:interrupt

analysis.tex:4 defines `countNFAcore*` as `countNFAcore` with the terminating condition
of line:interrupt deleted, so that `Σ_{r,q} |S^r(q)|` may grow past `θ`.  Its two
lemmas (proba_p(q), proba_S(q), analysis.tex:6-13) are about this variant, and
Lemma main_result_core (analysis.tex:23-39) transfers them to the real run.

* `corePairs A n` — the unrolled states `q^i`, `1 ≤ i ≤ n`, `q ∈ Q^i`, in the order
  `countNFAcore` visits them (layer by layer, `≺` within a layer).
* `runStar` / `coreLawStar` — `estimateAndSample` on each listed state in turn, from
  `initState`, never stopping.  The `stopped` flag stays `false`.
* `langCount A ℓ q` — `|L(q^ℓ)|`, the words of length `ℓ` reaching `q`.
* `goodWindow ε L` — the target window `[1/((1+ε/2)L), 1/((1−ε/2)L)]` for `p(q)`.
  It is the paper's `(1 ± ε)|L(q)|⁻¹` tightened to what its proof delivers (the
  loose-block event of analysis.tex:407-411 is at `ε/2`): it is the window that
  makes `1/p(q_F) ∈ (1 ± ε)|ℒ_n(𝒜)|`, which `(1 ± ε)|L|⁻¹` does not.
-/

set_option autoImplicit false

namespace Nfa.Analysis

open Nfa.Pseudocode

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- The unrolled states `q^i` (`1 ≤ i ≤ n`, `q ∈ Q^i`) in visiting order.

PAPER: algorithm.tex:97-100 (the loops `for 1 ≤ i ≤ n`, `for q ∈ Q^i`). -/
noncomputable def corePairs (A : PaperNFA Q) (n : ℕ) : List (ℕ × Q) :=
  (List.range' 1 n).flatMap fun i => (layerList A i).map fun q => (i, q)

/-- `estimateAndSample` on each listed state in turn, with no interrupt.

PAPER: analysis.tex:4 (`countNFAcore*`: `countNFAcore` without line:interrupt). -/
noncomputable def runStar (A : PaperNFA Q) (σ : Selector A) (P : Params) :
    CoreState Q → List (ℕ × Q) → PMF (CoreState Q)
  | st, [] => PMF.pure st
  | st, x :: xs => (estimateAndSample A σ P x.1 st x.2).bind fun st' => runStar A σ P st' xs

/-- **`countNFAcore*`**: the final state of one run of the core loop without
line:interrupt.

PAPER: analysis.tex:4. -/
noncomputable def coreLawStar (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ) :
    PMF (CoreState Q) :=
  runStar A σ P (initState A P) (corePairs A n)

end Nfa.Analysis

namespace Nfa.Analysis

/-- `|L(q^ℓ)|`: the number of words of length `ℓ` along which `q` is reachable from
`q_I`.

PAPER: background.tex:18, 32 (`L(q)` for `q` a state of the unrolled automaton). -/
noncomputable def langCount {Q : Type} (A : PaperNFA Q) (ℓ : ℕ) (q : Q) : ℕ :=
  {w : List Bool | w.length = ℓ ∧ q ∈ A.toNFA.eval w}.ncard

/-- The target window for `p(q)`: `[1/((1+ε/2)L), 1/((1−ε/2)L)]`.

INTERNAL: the paper's window `(1 ± ε)|L(q)|⁻¹` (analysis.tex:7) does not give
`1/p(q_F) ∈ (1 ± ε)|L|`; this one does, and is what the paper's `ε/2` loose-block
argument actually controls.
TEXLINE: analysis.tex:407-411 -/
def goodWindow (ε L : ℝ) : Set ℝ :=
  Set.Icc (1 / ((1 + ε / 2) * L)) (1 / ((1 - ε / 2) * L))

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · defined · `corePairs`, `runStar`, `coreLawStar`, `langCount`, `goodWindow`
-/
