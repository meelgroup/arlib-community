import Formalization3sum.Interface.Encoding
import Mathlib.Data.Finset.Dedup

/-!
# Set-valued view of the direct answer list

Correspondence ledger for the paper's algorithm transcript:

* Step 0 (04-general.tex:69,361), direct computation for `D = 1` and bounded
  small dimensions: `wantedAnswerSet` gives the specified values and
  `directAnswerSet` views `Program.directRun` through `directAnswers`.
* Steps 1–2 (04-general.tex:269–270), outer tiling and distinct inner-set
  assignments: **MODEL:** `Program` has no padding, tiles, or assignment.
* Step 3 (04-general.tex:271–272), shared encodings: **MODEL:** `Program` has no
  encoding routine.
* Steps 4–5 (04-general.tex:273–274), box initialization and trie recurrence:
  **MODEL:** `Program` has no box data structure or trie.
* Steps 6–8 (04-general.tex:275–280), query location and the low-order and box
  contributions: **MODEL:** `Program` has only `directEntry`; it cannot issue
  the paper's box query.
* Step 9 (04-general.tex:281), answer each requested position:
  `wantedAnswerSet` states the target set, while `directAnswerSet` is the
  set of writes made by `Program.directRun` in its direct branch.

There are two definitions because the program's answer carrier retains order:
its iteration and writes are charged operations. A future sealed dictionary
would likewise retain its insertion history and is not extensional as a set.
The correctness argument instead compares sets of position–value pairs, so
`List.toFinset` forgets this history. The ideal set and the direct run's set
are separate objects for the later correctness bridge to relate. This module
does not assert that the direct branch implements the missing sparse algorithm.
-/

set_option autoImplicit false

namespace Formalization3sum.Interface

open Formalization3sum.Model

/-- The paper's exact answer relation, restricted to the requested positions. -/
noncomputable def wantedAnswerSet {N D : ℕ} (a : Input N D) :
    Finset ((Fin N × Fin N) × ℤ) :=
  a.W.image (fun p => (p, wantedValue a p))

/-- The set of position–value writes from the implemented direct branch. -/
noncomputable def directAnswerSet {N D : ℕ} (a : Input N D) :
    Finset ((Fin N × Fin N) × ℤ) :=
  (directAnswers a).toFinset

end Formalization3sum.Interface
