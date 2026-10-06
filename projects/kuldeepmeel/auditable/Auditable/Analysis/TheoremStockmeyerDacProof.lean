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

/-!
# `Stock` solves DAC (Theorem [Stockmeyer], stock.tex:114-135)

`Stock(F)` is `AFCounter`'s stock loop on its own (`Model/Program.lean`): the same fold
of `stockStep (fPrime F)` over `List.range' 1 n'` from the empty register. The two
programs differ only in the default read off a loop that never succeeds (`0` for
`Stock`, `n'` for `AFCounter`). For `n' ≥ 1` that default is never read: round `n'`
succeeds, because the `n'` identity hashes isolate every point. So `Stock`'s `v` is
`AFCounter`'s `c_high` (`stockCounter_v_eq_afCounter_chigh`), and the accuracy bound is
`afCounter_dac_proof`, which is the paper's own route: combined.tex:60-64 proves
`AFCounter` correct by observing it returns the same `c_high` as Algorithm algo:stock.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable Auditable.Interface Auditable.Interface.Pseudocode Auditable.Program
open Auditable.Model.Operations

/-- INTERNAL: one round of `Charged.foldlWhile`'s value: stop with the register on `none`,
otherwise continue from the new register. arlib states only the `nil` case.
TEXLINE: stock.tex:89-97 -/
theorem val_foldlWhile_cons {κ κₛ α β : Type}
    (f : β → α → Arlib.Computation.Charged κ κₛ (Option β)) (a : α) (l : List α) (b : β) :
    (Arlib.Computation.Charged.foldlWhile f (a :: l) b).val =
      (match (f b a).val with
      | none => b
      | some b' => (Arlib.Computation.Charged.foldlWhile f l b').val) := by
  rw [Arlib.Computation.Charged.foldlWhile]
  split <;> rename_i heq <;> unfold Arlib.Computation.Charged.val <;> rw [heq]

/-- INTERNAL: the break-on-success stock loop ends with a recorded witness if it starts
with one, or if some round of its list succeeds.
TEXLINE: stock.tex:89-97 -/
theorem stockFold_isSome_of {N : ℕ} (G : CNF N) (l : List ℕ) (reg : StockReg N)
    (h : reg.isSome ∨ ∃ m ∈ l, stockSucceeds G m = true) :
    (Arlib.Computation.Charged.foldlWhile (stockStep G) l reg).val.isSome := by
  induction l generalizing reg with
  | nil =>
    rcases h with h | ⟨m, hm, -⟩
    · simpa using h
    · simp at hm
  | cons a l ih =>
    rw [val_foldlWhile_cons]
    cases reg with
    | some w => exact rfl
    | none =>
      rw [stockStep_none_val]
      apply ih
      rcases h with h | ⟨m, hm, hs⟩
      · simp at h
      · rcases List.mem_cons.mp hm with rfl | hm'
        · left
          unfold stockSucceeds at hs
          simpa using hs
        · right; exact ⟨m, hm', hs⟩

/-- INTERNAL: with `N ≥ 1`, round `N` of the stock loop succeeds: the `N` identity
hashes isolate every point.
TEXLINE: stock.tex:89-97 -/
theorem stockSucceeds_top {N : ℕ} (G : CNF N) (hN : 1 ≤ N) : stockSucceeds G N = true := by
  rw [stockSucceeds_iff]
  refine ⟨fun _ => identityHash N, fun z₁ _ => ⟨⟨0, hN⟩, fun z₂ _ hne => ?_⟩⟩
  simpa [identityHash_apply] using hne

/-- INTERNAL: for `n' ≥ 1`, `Stock(F)`'s `v` is `AFCounter(F)`'s `c_high`: the two
programs run the same stock loop, and it always records a success.
TEXLINE: combined.tex:60-64 -/
theorem stockCounter_v_eq_afCounter_chigh {n : ℕ} (F : CNF n) (hN : 1 ≤ nPrime n) :
    (Program.stockCounter F).val.v = (Program.afCounter F).val.chigh := by
  have hsome : (stockLoop (fPrime F)).val.isSome :=
    stockFold_isSome_of _ _ none
      (Or.inr ⟨nPrime n, List.mem_range'_1.mpr ⟨hN, by omega⟩, stockSucceeds_top _ hN⟩)
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
  rw [afCounter_val]
  show ((stockLoop (fPrime F)).val.getD ⟨0, fun i => i.elim0⟩).1 =
    ((stockLoop (fPrime F)).val.getD (stockDefault (nPrime n))).1
  rw [hw]
  rfl

end Auditable.Analysis

/-- PAPER: stock.tex:115, stock.tex:129-133 — **`Stock` solves DAC**: on a satisfiable `F`
over `n ≥ 4` variables, `CntEst = 2^{v / ⌈log₂ n⌉}` is within a factor `16` of `|sol F|`.
Proved through `AFCounter`, whose `c_high` is `Stock`'s `v` (`n' ≥ 8` here). -/
theorem Auditable.Analysis.stockmeyer_dac_proof (hprior : Prior) {n : ℕ} (hn : 4 ≤ n) (F : CNF n) (hsat : 1 ≤ solCount F) : (solCount F : ℝ) / 16 ≤ estimate (copies n) (Program.stockCounter F).val.v ∧ estimate (copies n) (Program.stockCounter F).val.v ≤ 16 * (solCount F : ℝ) := by
  have hN : 1 ≤ nPrime n := by
    unfold nPrime copies
    have := Nat.clog_pos (b := 2) (n := n) (by norm_num) (by omega)
    nlinarith
  rw [stockCounter_v_eq_afCounter_chigh F hN]
  exact afCounter_dac_proof hprior hn F hsat

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `v = c_high` of `afCounter` (stock loop always succeeds by `n'`), then `afCounter_dac_proof`
-/
