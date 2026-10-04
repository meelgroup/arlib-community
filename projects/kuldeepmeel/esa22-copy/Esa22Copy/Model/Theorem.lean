import Esa22Copy.Model.Prior
import Esa22Copy.Model.Prelude
import Esa22Copy.Model.Run
import Esa22Copy.Meta.ModelClosure
import Arlib.Prelude
import Esa22Copy.Analysis.TheoremSpaceProof
import Esa22Copy.Analysis.TheoremCorrectProof

/-!
# Theorem: F0-Estimator is an (ε,δ)-approximation in `thresh` sample cells

The theorem of esa22-final.tex:501-503:

> For any data stream `A` and any `0 < ε, δ < 1`, the algorithm F0-Estimator
> outputs an `(ε,δ)`-approximation of `F0(A)`.  The algorithm uses
> `O((1/ε²)·log n·(log m + log(1/δ)))` space in the worst case.

Two claims, and they are of different kinds:

* `f0Estimator_correct` — **can fail**: with probability at least `1 - δ` over
  the algorithm's coins (the law `Esa22Copy.output A ε δ`) the output is not ⊥
  and is a `c` with `(1-ε)·F0(A) ≤ c ≤ (1+ε)·F0(A)` (closed interval, Problem 1,
  esa22-final.tex:319-323; `Arlib.relErr`).
* `f0Estimator_space` — **cannot fail**: on every reachable run, the sample `X`
  never holds more than `thresh ε δ m` elements (`worstSpace` is a supremum over
  the support of `Esa22Copy.run A ε δ`).

`f0Estimator_main` is their conjunction, as the paper states it.

## Statement decisions

* **Space in cells, not an asymptotic in bits.**  The paper's
  `O((1/ε²) log n (log m + log 1/δ))` is `thresh · ⌈log₂ n⌉` bits with
  `thresh = ⌈(12/ε²) log₂(8m/δ)⌉` (esa22-final.tex:507).  The explicit bound
  `≤ thresh` sample cells is stated instead; bits = cells · ⌈log₂ n⌉ is a one-line
  conversion.  As in the paper, the bits for the level of `p`, the loop counter
  and the output register are not counted.  The literal big-O is degenerate for
  `n = 1` (bound 0) and for `m = 1, δ → 1`, so it is not stated as an `IsBigO`.
* **No `m ≥ 1` hypothesis**: for the empty stream the output is `some 0 = F0`.
* **No hypothesis on `F0`.**  The paper's Claim lm:error-fail needs
  `ℓ = ⌊log₂(4F0/thresh)⌋ ≥ 0`, which fails when `F0 < thresh/4`; the theorem
  still holds there (the run never halves `p` and outputs `F0` exactly), and the
  case split is the proof's business.
* `hprior : Prior` is first, and currently empty: nothing is assumed from prior
  work yet.
-/

set_option autoImplicit false

namespace Esa22Copy

open Arlib.Computation
open Esa22Copy.Model

/-- **Correctness**: F0-Estimator outputs an `(ε,δ)`-approximation of `F0(A)` —
with probability at least `1 - δ` it returns a number `c ≠ ⊥` with
`(1-ε)·F0(A) ≤ c ≤ (1+ε)·F0(A)`. -/
theorem f0Estimator_correct (hprior : Prior) {n : ℕ} (A : List (Fin n)) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      (output A ε δ).toOuterMeasure
        {o | ∃ c : ℕ, o = some c ∧ (c : ℝ) ∈ Arlib.relErr ε (F0 A : ℝ)} := by
    exact Esa22Copy.Analysis.f0Estimator_correct_proof hprior (n := n) A ε δ hε0 hε1 hδ0 hδ1

/-- **Worst-case space**: on every reachable run of F0-Estimator, the sample `X`
holds at most `thresh ε δ m = ⌈(12/ε²)·log₂(8m/δ)⌉` stream elements at every
point, `m = A.length`.  With `⌈log₂ n⌉` bits per element this is the paper's
`O((1/ε²)·log n·(log m + log(1/δ)))` bits. -/
theorem f0Estimator_space (hprior : Prior) {n : ℕ} (A : List (Fin n)) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    worstSpace (Arlib.Computation.Cell.cell : Operations.Cell) 0 (run A ε δ)
      ≤ (thresh ε δ A.length : ℕ∞) := by
    exact Esa22Copy.Analysis.f0Estimator_space_proof hprior (n := n) A ε δ hε0 hε1 hδ0 hδ1

/-- **The theorem of esa22-final.tex:501-503**: F0-Estimator outputs an
`(ε,δ)`-approximation of `F0(A)`, and holds at most `thresh ε δ m` stream
elements on every run. -/
theorem f0Estimator_main (hprior : Prior) {n : ℕ} (A : List (Fin n)) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
        (output A ε δ).toOuterMeasure
          {o | ∃ c : ℕ, o = some c ∧ (c : ℝ) ∈ Arlib.relErr ε (F0 A : ℝ)} ∧
      worstSpace (Arlib.Computation.Cell.cell : Operations.Cell) 0 (run A ε δ)
        ≤ (thresh ε δ A.length : ℕ∞) :=
  ⟨f0Estimator_correct hprior A ε δ hε0 hε1 hδ0 hδ1,
    f0Estimator_space hprior A ε δ hε0 hε1 hδ0 hδ1⟩

end Esa22Copy

#modelClosureOfType Esa22Copy.f0Estimator_main
#print axioms Esa22Copy.f0Estimator_main

#surplusIn Esa22Copy.Model from Esa22Copy.f0Estimator_main

/-!
HANDOFF NOTES
Statement match: Read on its own, the Lean says: for every n, every stream A over Fin n, and every real ε, δ in (0,1), (i) with probability at least 1-δ under the output law of the transcribed Algorithm 1 (threshold ⌈(12/ε²)·log₂(8m/δ)⌉, one fresh draw per item), the output is not ⊥ and is a natural number c in relErr ε F0(A). It also says (ii) on every run in the support, the peak number of sample cells (elements of X) is at most thresh ε δ m. The binders match the paper: every stream, every ε and δ in (0,1), every universe size n. `Prior` is empty, so there are no extra hypotheses. The correctness conjunct matches the paper's (ε,δ)-approximation, with ⊥ counted as failure, as the paper's Error event does. It is stated over the line-by-line transcription `Program.estimator`, not over Algorithm 2 or 3. The space conjunct is not the paper's claim, though. The paper asserts an asymptotic bound in bits, O((1/ε²)·log n·(log m + log 1/δ)). The Lean asserts an exact, non-asymptotic bound in sample cells: at most thresh elements. That is the fact the paper's proof uses ("the size of the set of samples … is always ≤ thresh"). Two steps are left outside the formal statement: 'bits = cells·⌈log₂ n⌉' and 'thresh = O((1/ε²)(log m + log 1/δ))'. So the log n factor and the bit-level claim are not formalized. This is a deliberate decision, explained in the Theorem.lean docstring. The Lean also surfaces a real boundary problem: the paper's literal O-bound degenerates at n = 1 (log n = 0, yet one cell is used) and at m = 1, δ → 1 (log m + log 1/δ → 0 while thresh ≥ 36/ε²). So the asymptotic as written needs unstated side conditions such as n ≥ 2 and a bounded-away δ or m ≥ 2. No user approval of this restatement is recorded, so the verdict cannot be 'formalized-with-approved-change'. If the user approves 'space = at most thresh stored stream elements', this becomes formalized-with-approved-change, and the remaining mismatches are notes. This verdict is about the statement only. Whether it is proved is for gate 2: the supplied `#print axioms` shows only [propext, Classical.choice, Quot.sound], but no `lake build` output was supplied to me.
Proof trust: 3 proof-trust issue(s), starting with lean/Esa22Copy/Meta/CostSeal.lean:217; lean/Esa22Copy/Meta/ModelClosure.lean:22,190
Randomness semantics: The headline's randomized object is a pushforward of a pre-drawn tape through a deterministic program: `run := (tapeLaw n (A.length+1) A.length).map (Program.estimator thr A)` and `output := (run …).map Charged.val`. This is not a PMF term built by composing `pure`, `bind` and primitive samplers. Line 4 ('with probability p, X ← X ∪ {a_i}') and line 6 ('throw away each element w.p. ½') are read-offs of externally supplied bits and a uniform subset. The output law therefore matches the paper only through an argument the reader must accept: zip pairing with a tape of length m, a block of length m+1 being long enough, uniform subset equals independent fair coins, and unread coins being harmless.
Audit surface: 2 surface theorem(s) do not match, starting with Esa22Copy.f0Estimator_space
-/
