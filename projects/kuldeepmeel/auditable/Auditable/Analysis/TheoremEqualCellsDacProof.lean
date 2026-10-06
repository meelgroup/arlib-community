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
import Auditable.Analysis.CellsExistAt

/-!
# `EqualCellsCounter` solves DAC (thm:intermediate, accuracy half)

The proof of bgp.tex:143-190, in three steps:

* **prop:bgp** (`cellsWith_bounds`): if every cell `α ∈ {0,1}^m` of a hash holds
  between `ℓ` and `u` solutions, then `ℓ · 2^m ≤ |sol F| ≤ u · 2^m` — the cells
  partition `sol F`.
* **The loop** (`cellsFold_witness`): `equalCellsCounter`'s fold stops at a round
  whose oracle answer is a witness `c` with `cellsWith`, provided some round in
  `[1, n]` admits one. The oracle searches every coefficient vector
  (`enumFun_complete`), so a round admitting a witness cannot be answered `none`.
* **A round admits a witness** (`cellsExist_round`): the paper's round
  `m₀ = ⌊log |sol F| − 12 − log n⌋` is `Nat.log 2 (|sol F| / 4096 n)`; it lies in
  `[1, n]` under `8192 n ≤ |sol F|`, and the probabilistic core at that round is
  `cellsExist_at` (`Auditable/Analysis/CellsExistAt.lean`), which rests on the
  cited Bellare–Rompel tail bound `bellareRompel_tail` and on the `n`-wise
  independence of `CellHash`, `cellHash_indep`.

With `ℓ = 1024 n`, `u = 16384 n` and `CntEst = ℓ · 2^m`, prop:bgp at the stopping
round is `|sol F| / 16 ≤ CntEst ≤ |sol F|`.
-/

set_option autoImplicit false

open Auditable.Model.Operations
open Arlib.Computation (Charged)

namespace Auditable.Analysis

/-- Every function whose values lie in `vals` is enumerated by `enumFun vals`.

INTERNAL: completeness of the exhaustive oracle search of `Model/Operations.lean`. -/
theorem enumFun_complete {α β : Type} [FinEnum α] (vals : List β)
    (hv : ∀ b, b ∈ vals) (f : α → β) : f ∈ enumFun vals := by
  unfold enumFun
  refine List.mem_map.2 ⟨fun a _ => f a, (List.mem_pi _ _).2 fun a _ => hv _, rfl⟩

/-- **prop:bgp**: a hash whose every cell holds between `l` and `u` solutions
witnesses `l · 2^m ≤ |sol F| ≤ u · 2^m`.

PAPER: bgp.tex:53-57 (Proposition prop:bgp), proof bgp.tex:59-72. -/
theorem cellsWith_bounds {K : Type} [Field K] {n : ℕ} (bits : K ≃ (Fin n → Bool))
    (F : CNF n) (l u m : ℕ) (c : CellHash K n) (h : cellsWith bits F l u m c) :
    l * 2 ^ m ≤ solCount F ∧ solCount F ≤ u * 2 ^ m := by
  classical
  have hsum : solCount F = ∑ α : Fin m → Bool, cellCount bits F c m α := by
    unfold solCount cellCount
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hcard : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by simp
  rw [hsum]
  constructor
  · calc l * 2 ^ m = ∑ _α : Fin m → Bool, l := by simp [hcard, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun α _ => (h α).1
  · calc _ ≤ ∑ _α : Fin m → Bool, u := Finset.sum_le_sum fun α _ => (h α).2
      _ = u * 2 ^ m := by simp [hcard, mul_comm]

/-- The round invariant of `equalCellsCounter`'s loop: a recorded witness passes
the check at the recorded round.

INTERNAL: loop analysis of `Program.equalCellsCounter`.
TEXLINE: bgp.tex:83-94 -/
theorem cellsFold_witness {K : Type} [Field K] [FinEnum K] {n : ℕ}
    (bits : K ≃ (Fin n → Bool)) (F : CNF n) (l : List ℕ) (reg : Program.CellsReg K n)
    (hinv : ∀ c, reg.2 = some c → cellsWith bits F (cellsLow n) (cellsHigh n) reg.1 c)
    (hex : reg.2.isSome ∨ ∃ m ∈ l, ∃ c, cellsWith bits F (cellsLow n) (cellsHigh n) m c) :
    ∃ c, (Charged.foldlWhile (Program.cellsStep bits F) l reg).val.2 = some c ∧
      cellsWith bits F (cellsLow n) (cellsHigh n)
        (Charged.foldlWhile (Program.cellsStep bits F) l reg).val.1 c := by
  induction l generalizing reg with
  | nil =>
      rcases hex with h | ⟨m, hm, -⟩
      · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
        exact ⟨c, hc, hinv c hc⟩
      · simp at hm
  | cons a l ih =>
      rcases reg with ⟨r1, r2⟩
      cases r2 with
      | some c' =>
          have hfold : (Charged.foldlWhile (Program.cellsStep bits F) (a :: l)
              (r1, some c')).val = (r1, some c') := rfl
          rw [hfold]
          exact ⟨c', rfl, hinv c' rfl⟩
      | none =>
          set res := (enumFun (α := Fin n) (FinEnum.toList K)).find? fun c =>
            decide (cellsWith bits F (cellsLow n) (cellsHigh n) a c) with hres
          have hfold : (Charged.foldlWhile (Program.cellsStep bits F) (a :: l)
              (r1, none)).val =
              (Charged.foldlWhile (Program.cellsStep bits F) l (a, res)).val := by
            cases h : res <;>
              simp [Charged.foldlWhile, Program.cellsStep, cellsOracle, Charged.val,
                ← hres, h] <;> rfl
          rw [hfold]
          apply ih
          · intro c hc
            have := List.find?_some (hres.symm.trans hc)
            simpa using this
          · rcases hex with h | ⟨m, hm, c, hc⟩
            · simp at h
            · rcases List.mem_cons.1 hm with rfl | hm
              · left
                cases h : res with
                | some _ => rfl
                | none =>
                    rw [hres, List.find?_eq_none] at h
                    exact absurd (by simpa using hc)
                      (h c (enumFun_complete _ FinEnum.mem_toList c))
              · exact Or.inr ⟨m, hm, c, hc⟩

/-- Some round `m ∈ [1, n]` admits a hash all of whose cells hold between
`ℓ = 1024 n` and `u = 16384 n` solutions.

INTERNAL: the choice `m₀ = ⌊log |sol F| − 12 − log n⌋` of bgp.tex:161-175, as
`Nat.log 2 (|sol F| / 4096 n)`, reduced to `cellsExist_at`.
TEXLINE: bgp.tex:153-190 -/
theorem cellsExist_round (hprior : Prior) {K : Type} [Field K] [FinEnum K] {n : ℕ}
    (bits : K ≃ (Fin n → Bool)) (hn : 4 ≤ n) (F : CNF n)
    (hcount : 8192 * n ≤ solCount F) :
    ∃ m ∈ List.range' 1 n, ∃ c, cellsWith bits F (cellsLow n) (cellsHigh n) m c := by
  have hS : solCount F ≤ 2 ^ n := by
    have := Finset.card_filter_le (Finset.univ : Finset (Assignment n))
      (fun σ => F.eval σ = true)
    simpa [solCount, sol] using this
  set S := solCount F with hSdef
  have hn0 : 0 < 4096 * n := by omega
  set q := S / (4096 * n) with hq
  have hq2 : 2 ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hn0]; linarith
  set m := Nat.log 2 q with hm
  have hpow : 2 ^ m ≤ q := Nat.pow_log_le_self 2 (by omega)
  have hlt : q < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have hqS : q * (4096 * n) ≤ S := Nat.div_mul_le_self S (4096 * n)
  have hSq : S < (q + 1) * (4096 * n) := by
    have := Nat.lt_div_mul_add (a := S) hn0
    rw [hq]; linarith
  have hm1 : 1 ≤ m := Nat.log_pos (by norm_num) hq2
  have hmn : m ≤ n := by
    have : 2 ^ m ≤ 2 ^ n := by nlinarith
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hlow : 4096 * n * 2 ^ m ≤ S := by nlinarith
  have hhigh : S < 8192 * n * 2 ^ m := by
    have : q + 1 ≤ 2 ^ (m + 1) := hlt
    rw [pow_succ] at this
    nlinarith
  obtain ⟨c, hc⟩ := cellsExist_at hprior bits hn F m hmn hlow hhigh
  exact ⟨m, List.mem_range'_1.2 ⟨hm1, by omega⟩, c, hc⟩

end Auditable.Analysis

/-- Proof-side owner for `Auditable.equalCells_dac`; its statement is fixed by the proof charter.

PAPER: bgp.tex:101-113 (thm:intermediate, "solves DAC"), proof bgp.tex:143-190. -/
theorem Auditable.Analysis.equalCells_dac_proof (hprior : Prior) {K : Type} [Field K] [FinEnum K] {n : ℕ} (bits : K ≃ (Fin n → Bool)) (hn : 4 ≤ n) (F : CNF n) (hcount : 8192 * n ≤ solCount F) : (solCount F : ℝ) / 16 ≤ ((Program.equalCellsCounter bits F).val.cntEst : ℝ) ∧ ((Program.equalCellsCounter bits F).val.cntEst : ℝ) ≤ (solCount F : ℝ) := by
  obtain ⟨c, -, hc⟩ := cellsFold_witness bits F (List.range' 1 n) (0, none)
    (fun c h => by cases h) (Or.inr (cellsExist_round hprior bits hn F hcount))
  have hest : (Program.equalCellsCounter bits F).val.cntEst =
      cellsLow n * 2 ^ (Charged.foldlWhile (Program.cellsStep bits F)
        (List.range' 1 n) (0, none)).val.1 := rfl
  obtain ⟨hlo, hhi⟩ := cellsWith_bounds bits F _ _ _ c hc
  rw [hest]
  generalize (Charged.foldlWhile (Program.cellsStep bits F) (List.range' 1 n) (0, none)).val.1 = M
    at hlo hhi ⊢
  simp only [cellsLow, cellsHigh] at hlo hhi ⊢
  have hlo' : (1024 * n * 2 ^ M : ℝ) ≤ solCount F := by exact_mod_cast hlo
  have hhi' : (solCount F : ℝ) ≤ 16384 * n * 2 ^ M := by exact_mod_cast hhi
  push_cast
  constructor <;> linarith

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `equalCells_dac_proof` closed; only open leaf below it is the cited `bellareRompel_tail` (proposed as a `Prior` field)
* r1 · split · parent assembled from `cellsWith_bounds`, `cellsFold_witness`, `cellsExist_round`; probabilistic core `cellsExist_at` in its own file
-/
