import Auditable.Model.Prelude
import Mathlib.Data.Fintype.BigOperators

/-!
# `|sol(MakeCopies(F, k))| = |sol F| ^ k`

`MakeCopies(F, k)` conjoins `k` copies of `F` on disjoint variable blocks
(stock.tex:106-111), so its solutions are exactly the `k`-tuples of solutions of `F`.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable

/-- INTERNAL: a satisfying assignment of `MakeCopies(F, k)` is one whose restriction to
every block `j` satisfies `F`.
TEXLINE: stock.tex:106-111 -/
theorem makeCopies_eval_iff {n : ℕ} (F : CNF n) (k : ℕ) (σ : Assignment (n * k)) :
    (makeCopies F k).eval σ = true ↔
      ∀ j : Fin k, F.eval (fun v => σ (finProdFinEquiv (v, j))) = true := by
  simp [makeCopies, CNF.eval, List.all_flatMap, List.all_map, Function.comp_def,
    List.any_map]

/-- INTERNAL: the block decomposition `{0,1}^{n·k} ≃ ({0,1}^n)^k` of `MakeCopies`.
TEXLINE: stock.tex:106-111 -/
def blockEquiv (n k : ℕ) : Assignment (n * k) ≃ (Fin k → Assignment n) where
  toFun σ j v := σ (finProdFinEquiv (v, j))
  invFun f i := f (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm i).1
  left_inv σ := by
    funext i
    show σ (finProdFinEquiv ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2)) = σ i
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv f := by funext j v; simp

/-- PAPER: finalaudit.tex:101 ("Noting that `|sol F'| = |sol F|^{log n}`"): the solutions
of `MakeCopies(F, k)` are the `k`-tuples of solutions of `F`. -/
theorem solCount_makeCopies {n : ℕ} (F : CNF n) (k : ℕ) :
    solCount (makeCopies F k) = solCount F ^ k := by
  unfold solCount
  rw [Finset.card_equiv (blockEquiv n k) (t := Fintype.piFinset fun _ : Fin k => sol F)]
  · exact Fintype.card_piFinset_const _ _
  · intro σ
    simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    rw [makeCopies_eval_iff]
    rfl

end Auditable.Analysis
