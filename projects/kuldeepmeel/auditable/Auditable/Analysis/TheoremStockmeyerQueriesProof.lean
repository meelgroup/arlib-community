import Auditable.Model.Prior
import Auditable.Model.Run
import Auditable.Meta.ModelClosure
import Auditable.Analysis.TheoremSoundProof
import Auditable.Analysis.TheoremCompleteProof
import Auditable.Analysis.TheoremOneQueryProof
import Auditable.Analysis.TheoremQuerySizeProof
import Auditable.Analysis.TheoremAfCounterDacProof
import Auditable.Analysis.TheoremAfCounterQueriesProof
import Auditable.Analysis.TheoremEqualCellsDacProof
import Auditable.Analysis.TheoremEqualCellsQueriesProof
import Auditable.Interface.Encoding
import Auditable.Interface.Pseudocode
import Auditable.Interface.ProgramModel

open Auditable.Model.Operations

open Arlib.Computation (Charged CostVec)

/-!
# `Stock`'s oracle tally

`Program.stockCounter` is one `Charged.foldlWhile (stockStep F')` over
`List.range' 1 (nPrime n)` followed by an uncharged `pure`. Each round costs at most
one `stockQuery` (`stockOracle`) and nothing else, so for every operation `o` the tally
is at most `nPrime n * CostVec.one Op.stockQuery o`: at most `nPrime n` stock queries,
and no holes or `Σ₂ᴾ` queries. `hprior` is not used.
-/

namespace Auditable.Analysis

/-- INTERNAL: the cons case of `Charged.foldlWhile`, read off through `.cost`; arlib
states only the `nil` case.
TEXLINE: stock.tex:89-97 -/
theorem stockCounter_cost_foldlWhile_cons {κ κₛ α β : Type}
    (f : β → α → Charged κ κₛ (Option β)) (a : α) (l : List α) (b : β) :
    (Charged.foldlWhile f (a :: l) b).cost =
      (match (f b a).val with
      | none => (f b a).cost
      | some b' => (f b a).cost + (Charged.foldlWhile f l b').cost) := by
  rw [Charged.foldlWhile]
  split <;> rename_i heq <;> unfold Charged.val at * <;> rw [heq] <;> rfl

/-- INTERNAL: one round of the stock loop charges at most one `stockQuery` and nothing
else (STK-4: one `2QBFCheck` call, or none once a witness is recorded).
TEXLINE: stock.tex:89-97 -/
theorem stockCounter_step_cost_le {N : ℕ} (G : CNF N) (reg : Program.StockReg N) (m : ℕ)
    (o : Op) : (Program.stockStep G reg m).cost o ≤ CostVec.one Op.stockQuery o := by
  unfold Program.stockStep
  rcases reg with _ | _
  · simp only [stockOracle, Charged.cost_bind, Charged.cost_op, CostVec.add_apply]
    split <;> simp
  · simp

/-- INTERNAL: the stock loop over `l` charges each operation `o` at most
`l.length * CostVec.one Op.stockQuery o`.
TEXLINE: stock.tex:89-97 -/
theorem stockCounter_fold_cost_le {N : ℕ} (G : CNF N) (o : Op) (l : List ℕ)
    (reg : Program.StockReg N) :
    (Charged.foldlWhile (Program.stockStep G) l reg).cost o ≤
      l.length * CostVec.one Op.stockQuery o := by
  induction l generalizing reg with
  | nil => simp
  | cons a l ih =>
      have hstep := stockCounter_step_cost_le G reg a o
      rw [stockCounter_cost_foldlWhile_cons]
      simp only [List.length_cons]
      split
      · exact hstep.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      · rename_i b' _
        rw [CostVec.add_apply]
        have := ih b'
        nlinarith

end Auditable.Analysis

/-- Proof-side owner for `Auditable.stockmeyer_queries`; its statement is fixed by the proof charter.

PAPER: stock.tex:84-103 (Algorithm `Stock`: one `2QBFCheck` per round of
`for m = 1 to n log n`, and no other oracle). -/
theorem Auditable.Analysis.stockmeyer_queries_proof (hprior : Prior) {n : ℕ} (F : CNF n) : (Program.stockCounter F).cost Op.stockQuery ≤ nPrime n ∧ (Program.stockCounter F).cost Op.holesQuery = 0 ∧ (Program.stockCounter F).cost Op.sigma2Query = 0 := by
  have key : ∀ o, (Program.stockCounter F).cost o ≤
      nPrime n * CostVec.one Op.stockQuery o := by
    intro o
    -- `makeCopies F (copies n)` must be read at `CNF (nPrime n)`, as in the program.
    have := Auditable.Analysis.stockCounter_fold_cost_le (N := nPrime n)
      (makeCopies F (copies n)) o (List.range' 1 (nPrime n)) none
    rw [List.length_range'] at this
    simp only [Program.stockCounter, Charged.cost_bind, Charged.cost_pure, CostVec.add_apply,
      CostVec.zero_apply, add_zero]
    exact this
  refine ⟨?_, ?_, ?_⟩
  · simpa using key Op.stockQuery
  · simpa using key Op.holesQuery
  · simpa using key Op.sigma2Query

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `stockmeyer_queries_proof` by induction on the stock loop, per-op bound `nPrime n * CostVec.one Op.stockQuery o`
-/
