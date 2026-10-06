import Auditable.Model.Prior
import Auditable.Model.Run
import Auditable.Meta.ModelClosure
import Auditable.Analysis.TheoremSoundProof
import Auditable.Analysis.TheoremCompleteProof
import Auditable.Analysis.TheoremOneQueryProof
import Auditable.Analysis.TheoremQuerySizeProof
import Auditable.Analysis.TheoremAfCounterDacProof
import Auditable.Analysis.TheoremAfCounterQueriesProof
import Auditable.Interface.Encoding
import Auditable.Interface.Pseudocode
import Auditable.Interface.ProgramModel

open Auditable.Model.Operations
open Arlib.Computation (Charged CostVec Rate)

/-- Proof-side owner for `Auditable.equalCells_queries`; its statement is fixed by the proof charter.

`equalCellsCounter` is one `Charged.foldlWhile (cellsStep bits F)` over `List.range' 1 n`
followed by an uncharged `pure`, and each round asks at most one `cellsOracle` (one
`cellsQuery`). The bound is Arlib's `Charged.steps_foldlWhile_le` at the unit rate,
which on the one-constructor currency `CellsOp` is exactly the `cellsQuery` tally. -/
theorem Auditable.Analysis.equalCells_queries_proof (hprior : Prior) {K : Type} [Field K] [FinEnum K] {n : ℕ} (bits : K ≃ (Fin n → Bool)) (F : CNF n) : (Program.equalCellsCounter bits F).cost CellsOp.cellsQuery ≤ n := by
  let _ : Fintype CellsOp := ⟨{CellsOp.cellsQuery}, fun o => by cases o; simp⟩
  -- At the unit rate, the step count of a `CellsOp` tally is its `cellsQuery` entry.
  have hsteps : ∀ c : CostVec CellsOp,
      CostVec.steps (Rate.unit CellsOp) c = c CellsOp.cellsQuery := by
    intro c
    rw [CostVec.steps_unit]
    show ∑ o ∈ ({CellsOp.cellsQuery} : Finset CellsOp), c o = _
    simp
  have hstep : ∀ reg m,
      Charged.steps (Rate.unit CellsOp) (Program.cellsStep bits F reg m) ≤ 1 := by
    intro reg m
    simp only [Charged.steps, hsteps]
    unfold Program.cellsStep
    rcases reg with ⟨k, _ | c⟩
    · simp only [cellsOracle, Charged.cost_bind, Charged.cost_op, CostVec.add_apply]
      split <;> simp
    · simp
  have hloop :=
    Charged.steps_foldlWhile_le (Rate.unit CellsOp) hstep (List.range' 1 n) (0, none)
  simp only [Charged.steps, hsteps] at hloop
  simpa [Program.equalCellsCounter] using hloop

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `equalCells_queries_proof` via `Charged.steps_foldlWhile_le` at `Rate.unit CellsOp`
-/
