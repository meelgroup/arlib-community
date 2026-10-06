import Auditable.Model.Prior
import Auditable.Model.Run
import Auditable.Meta.ModelClosure
import Auditable.Interface.Encoding
import Auditable.Interface.Pseudocode
import Auditable.Interface.ProgramModel
import Auditable.Analysis.HolesExist
import Auditable.Analysis.StockExist

/-!
# Completeness of `CountAuditor` on `AFCounter`'s own certificate

On a satisfiable `F` (`n ≥ 12`), the auditor verifies the certificate `AFCounter(F)`
returns. Through the bridge `countAuditor_afCounter_val_eq_verdict_result` this is the
pseudocode statement `verdict F (result F) = verified`, i.e. three facts about the
honest run on `G = F'`:

* **poscheck**: the stock loop's output isolates every solution. At the first success
  `c_high` this is the oracle's witness; if no round succeeds, the default identity
  hashes at `c_high = n'` isolate every point (`identityHash_apply`).
* **negcheck**: the holes loop's output hits every cell. At `c_low = m − 1` for the first
  failing `m` this is the witness of round `m − 1` (round `0`, if `m = 1`, holds because
  `G` is satisfiable, `holes_exist` at `m = 0`); with no failure it is round `n'`.
* **gap** `c_high ≤ c_low + 7`, in fact `≤ c_low + 2`: round `m = c_low + 1` of the holes
  loop failed, so `|sol G| < 2^{c_low + 1}` (contrapositive of `holes_exist`); then
  `2 |sol G| ≤ 2^{c_low + 2}`, so round `c_low + 2` of the stock loop succeeds
  (`stock_exist`), and the stock loop stops no later than that.

The paper's proof of thm:finalaudit (finalaudit.tex:82-109) does not argue completeness;
the gap is the gap lemma combined.tex:117-132, here with the existence lemmas in the
sharper counting forms of `HolesExist.lean` and `StockExist.lean`. Turning an oracle's
`none` into "no witness exists" uses that the oracles search the whole hash family
(`mem_allHashTuples`).
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable Auditable.Interface Auditable.Interface.Pseudocode Auditable.Program
open Auditable.Model.Operations

/-! ## The oracles search the whole hash family -/

/-- INTERNAL: `enumFun vals` lists every function whose values lie in `vals`.
TEXLINE: finalaudit.tex:17-29 -/
theorem mem_enumFun {α β : Type} [FinEnum α] (vals : List β) (f : α → β)
    (hf : ∀ a, f a ∈ vals) : f ∈ enumFun vals := by
  unfold enumFun
  rw [List.mem_map]
  exact ⟨fun a _ => f a, (List.mem_pi _ _).mpr fun a _ => hf a, rfl⟩

/-- INTERNAL: every tuple of affine hashes is in the oracles' search space.
TEXLINE: combined.tex:32, combined.tex:41 -/
theorem mem_allHashTuples (c N m : ℕ) (hs : Fin c → AffHash N m) :
    hs ∈ allHashTuples c N m := by
  have hbool : ∀ x : Bool, x ∈ [false, true] := by intro x; cases x <;> simp
  apply mem_enumFun
  intro i
  obtain ⟨A, b⟩ := hs i
  unfold allHashes
  rw [List.mem_flatMap]
  exact ⟨A, mem_enumFun _ _ fun r => mem_enumFun _ _ fun j => hbool _,
    List.mem_map.mpr ⟨b, mem_enumFun _ _ fun _ => hbool _, rfl⟩⟩

/-- INTERNAL: `3QBFCheck(φ_holes^G(m))` answers iff a witness exists.
TEXLINE: combined.tex:32 -/
theorem holesAnswer_isSome_iff {N : ℕ} (G : CNF N) (m : ℕ) :
    (holesAnswer G m).isSome ↔ ∃ hs, holesWith G m hs := by
  unfold holesAnswer
  rw [List.find?_isSome]
  constructor
  · rintro ⟨hs, -, h⟩; exact ⟨hs, of_decide_eq_true h⟩
  · rintro ⟨hs, h⟩; exact ⟨hs, mem_allHashTuples _ _ _ hs, decide_eq_true h⟩

/-- INTERNAL: `2QBFCheck(φ_stock^G(m))` answers iff a witness exists.
TEXLINE: combined.tex:41 -/
theorem stockAnswer_isSome_iff {N : ℕ} (G : CNF N) (m : ℕ) :
    (stockAnswer G m).isSome ↔ ∃ hs, stockWith G m hs := by
  unfold stockAnswer
  rw [List.find?_isSome]
  constructor
  · rintro ⟨hs, -, h⟩; exact ⟨hs, of_decide_eq_true h⟩
  · rintro ⟨hs, h⟩; exact ⟨hs, mem_allHashTuples _ _ _ hs, decide_eq_true h⟩

/-- INTERNAL: when a holes witness exists, the recorded witness is one.
TEXLINE: combined.tex:32-37 -/
theorem holesWith_witnessAt {N : ℕ} (G : CNF N) (j : ℕ) (h : ∃ hs, holesWith G j hs) :
    holesWith G j (holesWitnessAt G j) := by
  obtain ⟨hs, hhs⟩ := Option.isSome_iff_exists.mp ((holesAnswer_isSome_iff G j).mpr h)
  have hw : holesWith G j hs := by
    unfold holesAnswer at hhs
    have h1 := List.find?_some hhs
    exact of_decide_eq_true h1
  unfold holesWitnessAt holesRet
  rw [hhs]
  exact hw

/-- INTERNAL: when a stock witness exists, the recorded witness is one.
TEXLINE: combined.tex:41-46 -/
theorem stockWith_witnessAt {N : ℕ} (G : CNF N) (j : ℕ) (h : ∃ hs, stockWith G j hs) :
    stockWith G j (stockWitnessAt G j) := by
  obtain ⟨hs, hhs⟩ := Option.isSome_iff_exists.mp ((stockAnswer_isSome_iff G j).mpr h)
  have hw : stockWith G j hs := by
    unfold stockAnswer at hhs
    have h1 := List.find?_some hhs
    exact of_decide_eq_true h1
  unfold stockWitnessAt stockRet
  rw [hhs]
  exact hw

/-- INTERNAL: a holes round fails iff no witness exists.
TEXLINE: combined.tex:33 -/
theorem holesFails_iff {N : ℕ} (G : CNF N) (m : ℕ) :
    holesFails G m = true ↔ ¬ ∃ hs, holesWith G m hs := by
  rw [← holesAnswer_isSome_iff]
  unfold holesFails holesRet
  cases holesAnswer G m <;> simp

/-- INTERNAL: a stock round succeeds iff a witness exists.
TEXLINE: combined.tex:42 -/
theorem stockSucceeds_iff {N : ℕ} (G : CNF N) (m : ℕ) :
    stockSucceeds G m = true ↔ ∃ hs, stockWith G m hs := by
  rw [← stockAnswer_isSome_iff]
  rfl

/-! ## The identity hash and satisfiability of `F'` -/

/-- INTERNAL: the stock loop's default hash (`A = I`, `b = 0`) is the identity map.
TEXLINE: combined.tex:23-52 -/
theorem identityHash_apply (N : ℕ) (z : Fin N → Bool) : (identityHash N).apply z = z := by
  funext i
  rw [AffHash.apply_eq]
  have hfun : (fun j => (identityHash N).A i j && z j) = fun j => if j = i then z i else false := by
    funext j
    by_cases h : j = i
    · subst h; simp [identityHash]
    · simp [identityHash, h, Ne.symm h]
  simp only [rowParity, hfun, xorFold_single _ (List.nodup_finRange N), List.mem_finRange,
    if_true]
  simp [identityHash]

/-- INTERNAL: `MakeCopies(F, k)` is satisfiable when `F` is: copy a solution into every
block.
TEXLINE: stock.tex:106-111 -/
theorem solCount_makeCopies_pos {n : ℕ} (F : CNF n) (k : ℕ) (hsat : 1 ≤ solCount F) :
    1 ≤ solCount (makeCopies F k) := by
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hsat
  apply Finset.card_pos.mpr
  refine ⟨fun v => σ (finProdFinEquiv.symm v).1, ?_⟩
  simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  simp only [CNF.eval, List.all_eq_true, List.any_eq_true] at hσ
  simp only [makeCopies, CNF.eval, List.all_eq_true, List.mem_flatMap, List.mem_map,
    List.any_eq_true]
  rintro c ⟨j, -, c₀, hc₀, rfl⟩
  obtain ⟨l, hl, hlσ⟩ := hσ c₀ hc₀
  exact ⟨_, List.mem_map.mpr ⟨l, hl, rfl⟩, by simpa using hlσ⟩

/-- INTERNAL: `F' = MakeCopies(F, log n)` is satisfiable when `F` is.
TEXLINE: stock.tex:106-111 -/
theorem solCount_fPrime_pos {n : ℕ} (F : CNF n) (hsat : 1 ≤ solCount F) :
    1 ≤ solCount (fPrime F) :=
  solCount_makeCopies_pos F (copies n) hsat

/-! ## What the two loops of the honest run return -/

/-- INTERNAL: a failing holes round `m` means fewer than `2^m` solutions
(contrapositive of lm:holesexist).
TEXLINE: combined.tex:117-132 -/
theorem holesFails_lt {N : ℕ} (G : CNF N) (m : ℕ) (h : holesFails G m = true) :
    solCount G < 2 ^ m := by
  by_contra hge
  push Not at hge
  exact (holesFails_iff G m).mp h (holes_exist G m hge)

/-- INTERNAL: the holes loop stops at `c_low = n'`, or else round `c_low + 1` failed.
TEXLINE: combined.tex:28-37 -/
theorem holesResult_clow {N : ℕ} (G : CNF N) :
    (holesResult G).1 = N ∨ solCount G < 2 ^ ((holesResult G).1 + 1) := by
  unfold holesResult
  cases hb : holesBreak G with
  | none => exact Or.inl rfl
  | some m =>
    right
    unfold holesBreak loopRange at hb
    rw [List.find?_range'_eq_some, List.mem_range'_1] at hb
    obtain ⟨hf, hmem, -⟩ := hb
    show solCount G < 2 ^ (m - 1 + 1)
    rw [Nat.sub_add_cancel hmem.1]
    exact holesFails_lt G m hf

/-- INTERNAL: **negcheck on the honest certificate**: the holes loop's output hits every
cell, when `G` is satisfiable and the loop is nonempty.
TEXLINE: combined.tex:28-37 -/
theorem holesResult_with {N : ℕ} (G : CNF N) (hS : 1 ≤ solCount G) (hN : 1 ≤ N) :
    holesWith G (holesResult G).1 (holesResult G).2 := by
  unfold holesResult
  cases hb : holesBreak G with
  | none =>
    unfold holesBreak loopRange at hb
    rw [List.find?_range'_eq_none] at hb
    have hN' := hb N hN (by omega)
    show holesWith G N (holesWitnessAt G N)
    apply holesWith_witnessAt
    by_contra hno
    rw [← holesFails_iff] at hno
    simp [hno] at hN'
  | some m =>
    unfold holesBreak loopRange at hb
    rw [List.find?_range'_eq_some, List.mem_range'_1] at hb
    obtain ⟨-, hmem, hmin⟩ := hb
    show holesWith G (m - 1) (holesWitnessAt G (m - 1))
    apply holesWith_witnessAt
    rcases Nat.lt_or_ge (m - 1) 1 with h0 | h1
    · have : m - 1 = 0 := by omega
      rw [this]
      exact holes_exist G 0 (by simpa using hS)
    · have := hmin (m - 1) h1 (by omega)
      by_contra hno
      rw [← holesFails_iff] at hno
      simp [hno] at this

/-- INTERNAL: **poscheck on the honest certificate**: the stock loop's output (with its
default) isolates every solution, when the loop is nonempty.
TEXLINE: combined.tex:39-47 -/
theorem stockResult_with {N : ℕ} (G : CNF N) (hN : 1 ≤ N) :
    stockWith G (stockResult G).1 (stockResult G).2 := by
  unfold stockResult
  cases hb : stockBreak G with
  | none =>
    intro z₁ _
    refine ⟨⟨0, hN⟩, fun z₂ _ hne => ?_⟩
    simpa [stockDefault, identityHash_apply] using hne
  | some m =>
    unfold stockBreak loopRange at hb
    rw [List.find?_range'_eq_some] at hb
    exact stockWith_witnessAt G m ((stockSucceeds_iff G m).mp hb.1)

/-- INTERNAL: the stock loop's `c_high` never exceeds the loop bound `n'`.
TEXLINE: combined.tex:39-47 -/
theorem stockResult_le {N : ℕ} (G : CNF N) : (stockResult G).1 ≤ N := by
  unfold stockResult
  cases hb : stockBreak G with
  | none => exact le_rfl
  | some m =>
    unfold stockBreak loopRange at hb
    rw [List.find?_range'_eq_some, List.mem_range'_1] at hb
    show m ≤ N
    omega

/-- INTERNAL: the stock loop stops at the **first** succeeding round.
TEXLINE: combined.tex:39-47 -/
theorem stockResult_min {N : ℕ} (G : CNF N) (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N)
    (hj : stockSucceeds G j = true) : (stockResult G).1 ≤ j := by
  unfold stockResult
  cases hb : stockBreak G with
  | none =>
    unfold stockBreak loopRange at hb
    rw [List.find?_range'_eq_none] at hb
    have := hb j hj1 (by omega)
    simp [hj] at this
  | some m =>
    unfold stockBreak loopRange at hb
    rw [List.find?_range'_eq_some] at hb
    obtain ⟨-, -, hmin⟩ := hb
    show m ≤ j
    by_contra hlt
    push Not at hlt
    have := hmin j hj1 hlt
    simp [hj] at this

/-- INTERNAL: **the gap lemma for the honest run**, `c_high ≤ c_low + 2`.
TEXLINE: combined.tex:117-132 -/
theorem result_gap {N : ℕ} (G : CNF N) :
    (stockResult G).1 ≤ (holesResult G).1 + 2 := by
  rcases holesResult_clow G with hc | hc
  · rw [hc]; have := stockResult_le G; omega
  · set c := (holesResult G).1
    have hsucc : stockSucceeds G (c + 2) = true := by
      rw [stockSucceeds_iff]
      apply stock_exist
      rw [pow_succ]
      omega
    by_cases hcN : c + 2 ≤ N
    · exact stockResult_min G (c + 2) (by omega) hcN hsucc
    · have := stockResult_le G; omega

/-- INTERNAL: **completeness, pseudocode form**: on a satisfiable `F` with `n ≥ 12`, the
auditor's verdict on the counter's certificate is `Verified`.
TEXLINE: combined.tex:117-132 -/
theorem verdict_result_eq_verified {n : ℕ} (hn : 12 ≤ n) (F : CNF n) (hsat : 1 ≤ solCount F) :
    verdict F (result F) = Verdict.verified := by
  have hS := solCount_fPrime_pos F hsat
  have hN : 1 ≤ nPrime n := by
    unfold nPrime copies
    have := Nat.clog_pos (b := 2) (n := n) (by norm_num) (by omega)
    nlinarith
  unfold verdict
  rw [if_pos]
  refine ⟨⟨stockResult_with _ hN, holesResult_with _ hS hN⟩, ?_⟩
  show (stockResult (fPrime F)).1 ≤ (holesResult (fPrime F)).1 + 7
  have := result_gap (fPrime F)
  omega

end Auditable.Analysis

/-- PAPER: problem.tex:28-31, combined.tex:117-132 — **completeness** of
`CountAuditor` (Algorithm algo:lonely-audit) on the certificate of `AFCounter`
(Algorithm algo:pigeons): on a satisfiable `F`, the auditor verifies it. The paper's
proof of thm:finalaudit (finalaudit.tex:82-109) assumes rather than proves it. -/
theorem Auditable.Analysis.finalAudit_complete_proof (hprior : Prior) {n : ℕ} (hn : 12 ≤ n) (F : CNF n) (hsat : 1 ≤ solCount F) : (Program.countAuditor F (Program.afCounter F).val).val = Verdict.verified := by
  rw [countAuditor_afCounter_val_eq_verdict_result]
  exact verdict_result_eq_verified hn F hsat


/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · via `holes_exist`/`stock_exist` (counting forms) and the bridge; gap is `≤ 2`
-/
