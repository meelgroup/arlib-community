import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Esa22Copy.Analysis.PreludeProof

/-!
# Prelude: the threshold and the number of distinct elements

The two non-library symbols the headline is stated in.

* `thresh ε δ m` — the sample capacity of Algorithm 1 (F0-Estimator), line 1:
  `thresh ← ⌈(12/ε²) log(8m/δ)⌉`, with `log = log₂` (esa22-final.tex:327).
* `F0 A` — the number of distinct elements of the stream (esa22-final.tex:316).

## Correspondence ledger

| paper | Lean |
|---|---|
| stream `A = ⟨a₁,…,a_m⟩`, `aᵢ ∈ [n]` | `A : List (Fin n)` (relabelling `[n]` as `Fin n`), `m = A.length` |
| `thresh = ⌈(12/ε²) log(8m/δ)⌉` (Alg. 1 line 1) | `Esa22Copy.thresh ε δ A.length` |
| `F0(A) = \|{a₁,…,a_m}\|` | `Esa22Copy.F0 A = A.toFinset.card` |

**`thresh` lives here and not in the program.**  It is a real-valued ceiling of a
`log₂`, which Lean cannot compute; `Model/Program.lean` takes the threshold as a
plain `ℕ` argument and `Model/Run.lean` instantiates it with exactly
`thresh ε δ A.length` (modelling note, not a paper deviation).

**Empty stream.**  For `m = 0` the paper's `log₂(8·0/δ)` is undefined.  Lean's
junk value `Real.logb 2 0 = 0` gives `thresh = 0`; the loop never runs, so this is
harmless, and the headline carries no `m ≥ 1` hypothesis (statement decision).
-/

namespace Esa22Copy

/-! ## Vocabulary -/

/-- **The sample capacity** `thresh = ⌈(12/ε²)·log₂(8m/δ)⌉` of Algorithm 1, line 1
(esa22-final.tex:427), for a stream of length `m`.  The logarithm is base 2 by the
paper's convention (esa22-final.tex:327). -/
noncomputable def thresh (ε δ : ℝ) (m : ℕ) : ℕ :=
  ⌈(12 / ε ^ 2) * Real.logb 2 (8 * (m : ℝ) / δ)⌉₊

/-! ## The quantity -/

/-- **`F0(A)`, the number of distinct elements of the stream** `A`
(esa22-final.tex:316): `|{a₁,…,a_m}|`. -/
def F0 {n : ℕ} (A : List (Fin n)) : ℕ := A.toFinset.card

/-- Cross-check of `F0` against Mathlib's other spelling of the distinct count,
`List.dedup.length` (compare `List.card_toFinset`). -/
theorem F0_eq_dedup_length {n : ℕ} (A : List (Fin n)) : F0 A = A.dedup.length := by
    exact Esa22Copy.Analysis.F0_eq_dedup_length_proof (n := n) A

end Esa22Copy
