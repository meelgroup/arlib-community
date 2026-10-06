import Auditable.Model.Prior
import Auditable.Model.Run
import Auditable.Meta.ModelClosure
import Auditable.Analysis.TheoremSoundProof
import Auditable.Analysis.TheoremCompleteProof
import Auditable.Analysis.TheoremOneQueryProof
import Auditable.Analysis.TheoremQuerySizeProof
import Auditable.Interface.Encoding
import Auditable.Interface.Pseudocode
import Auditable.Interface.ProgramModel
import Auditable.Analysis.StockNecessary
import Auditable.Analysis.StockExist
import Auditable.Analysis.SolCountMakeCopies

/-!
# `AFCounter` solves DAC (combined.tex:60-64, stock.tex:117-133)

`AFCounter(F)`'s `c_high` is the first `m ∈ [1, n']` at which `φ_stock^{F'}(m)` has a
witness (the `stockResult` of `Interface/Pseudocode.lean`), with `F' = MakeCopies(F, k)`,
`k = ⌈log₂ n⌉`, `n' = n · k`. The proof is the one of Theorem [Stockmeyer]
(stock.tex:117-133), to which the paper's proof of the theorem after algo:pigeons
defers:

* **lower bound** — at `c_high` the stock check succeeded, so by cl:stockup
  (`stock_necessary`) `|sol F'| ≤ c_high · 2^{c_high} ≤ n' · 2^{c_high}`;
* **upper bound** — at `c_high − 1` it failed (or `c_high = 1`), so by the
  contrapositive of lm:stockexist (`stock_exist`, hypothesis `2 |sol| ≤ 2^m`)
  `2^{c_high} ≤ 4 · |sol F'|`. If no round succeeds, `c_high = n'` and the round `n'`
  itself failed, which gives the same bound;
* **root-taking** — `|sol F'| = |sol F|^k` (`solCount_makeCopies`), and
  `n' = n k ≤ 2^k · 8^k = 16^k` because `n ≤ 2^k` for the ceiling log; taking `k`-th
  roots gives `|sol F| / 16 ≤ 2^{c_high / k} ≤ 4^{1/k} |sol F| ≤ 16 |sol F|`.

The gap `c_high − c_low ≤ 7` is not used: the bound needs only the stock loop.
`hsat` makes `|sol F'| ≥ 1`, which the `c_high = 1` case needs. `hprior` is unused.
-/

set_option autoImplicit false

namespace Auditable.Analysis.AfCounterDac

open Auditable Auditable.Interface Auditable.Interface.Pseudocode Auditable.Model.Operations

/-- INTERNAL: `enumFun vals` lists every function all of whose values are in `vals`.
TEXLINE: stock.tex:188-191 -/
theorem enumFun_complete {α β : Type} [FinEnum α] (vals : List β) (f : α → β)
    (h : ∀ a, f a ∈ vals) : f ∈ enumFun vals := by
  unfold enumFun
  exact List.mem_map.2 ⟨fun a _ => f a, (List.mem_pi _ _).2 fun a _ => h a, rfl⟩

/-- INTERNAL: `allHashes N m` lists every affine hash.
TEXLINE: prelim.tex:82-118 -/
theorem allHashes_complete {N m : ℕ} (h : AffHash N m) : h ∈ allHashes N m := by
  unfold allHashes
  refine List.mem_flatMap.2 ⟨h.A, enumFun_complete _ _ fun i => enumFun_complete _ _ fun j => ?_, ?_⟩
  · cases h.A i j <;> simp
  · refine List.mem_map.2 ⟨h.b, enumFun_complete _ _ fun i => ?_, rfl⟩
    cases h.b i <;> simp

/-- INTERNAL: a `ret = 0` answer of `2QBFCheck(φ_stock(m))` means no witness exists.
TEXLINE: combined.tex:41 -/
theorem stockRet_none_not {N : ℕ} (G : CNF N) (m : ℕ) (h : stockRet G m = none)
    (hs : Fin m → AffHash N m) : ¬ stockWith G m hs := by
  intro hw
  have := List.find?_eq_none.1 h hs (enumFun_complete _ _ fun _ => allHashes_complete _)
  exact this (decide_eq_true hw)

/-- INTERNAL: a returned witness of `2QBFCheck(φ_stock(m))` is a witness.
TEXLINE: combined.tex:41 -/
theorem stockRet_some_with {N : ℕ} (G : CNF N) (m : ℕ) (hs : Fin m → AffHash N m)
    (h : stockRet G m = some hs) : stockWith G m hs := by
  unfold stockRet stockAnswer at h
  exact of_decide_eq_true (List.find?_some (p := fun hs => decide (stockWith G m hs)) h)

/-- INTERNAL: at most `2^N` assignments satisfy a CNF over `N` variables.
TEXLINE: prelim.tex:2-8 -/
theorem solCount_le_pow_vars {N : ℕ} (G : CNF N) : solCount G ≤ 2 ^ N := by
  unfold solCount sol
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- INTERNAL: what the stock loop's stopping index `c_high` satisfies: `c_high ≤ N`,
`|sol G| ≤ c_high · 2^{c_high}` (cl:stockup at the success), and
`2^{c_high} ≤ 4 |sol G|` (lm:stockexist at the failure just before it).
TEXLINE: stock.tex:117-133 -/
theorem stockResult_bounds {N : ℕ} (hN : 1 ≤ N) (G : CNF N) (hS : 1 ≤ solCount G) :
    (stockResult G).1 ≤ N ∧ solCount G ≤ (stockResult G).1 * 2 ^ (stockResult G).1 ∧
      2 ^ (stockResult G).1 ≤ 4 * solCount G := by
  have fails : ∀ j, stockSucceeds G j = false → 2 ^ j < 2 * solCount G := by
    intro j hj
    by_contra hle
    obtain ⟨hs, hw⟩ := stock_exist G j (by omega)
    have hnone : stockRet G j = none := by
      simpa [stockSucceeds] using hj
    exact stockRet_none_not G j hnone hs hw
  unfold stockResult
  cases hb : stockBreak G with
  | none =>
    simp only [stockDefault]
    unfold stockBreak loopRange at hb
    have hN' := List.find?_range'_eq_none.1 hb N hN (by omega)
    have := fails N (by simpa using hN')
    exact ⟨le_rfl, (solCount_le_pow_vars G).trans (Nat.le_mul_of_pos_left _ hN), by omega⟩
  | some m =>
    dsimp only
    unfold stockBreak loopRange at hb
    obtain ⟨hsucc, hmem, hmin⟩ := List.find?_range'_eq_some.1 hb
    rw [List.mem_range'_1] at hmem
    obtain ⟨hs, hhs⟩ : ∃ hs, stockRet G m = some hs := by
      simpa [stockSucceeds, Option.isSome_iff_exists] using hsucc
    have hw : stockWith G m (stockWitnessAt G m) := by
      rw [stockWitnessAt, hhs]; exact stockRet_some_with G m hs hhs
    refine ⟨by omega, stock_necessary G m _ hw, ?_⟩
    rcases Nat.lt_or_ge m 2 with hm | hm
    · obtain rfl : m = 1 := by omega
      omega
    · have h1 := fails (m - 1) (by simpa using hmin (m - 1) (by omega) (by omega))
      have : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega

/-- INTERNAL: `(2^{c/k})^k = 2^c`.
TEXLINE: combined.tex:48 -/
theorem estimate_pow (k c : ℕ) (hk : 1 ≤ k) : estimate k c ^ k = (2 : ℝ) ^ c := by
  unfold estimate
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ (by positivity),
    Real.rpow_natCast]

/-- INTERNAL: the root-taking step. From `S^k ≤ c 2^c`, `c ≤ n k`, `n ≤ 2^k` and
`2^c ≤ 4 S^k`, the estimate `2^{c/k}` is within a factor `16` of `S`.
TEXLINE: stock.tex:121-133 -/
theorem dac_arith (n k S c : ℕ) (hk : 1 ≤ k) (hnk : n ≤ 2 ^ k) (hc : c ≤ n * k)
    (hlow : S ^ k ≤ c * 2 ^ c) (hup : 2 ^ c ≤ 4 * S ^ k) :
    (S : ℝ) / 16 ≤ estimate k c ∧ estimate k c ≤ 16 * (S : ℝ) := by
  have hk0 : k ≠ 0 := by omega
  have hx : 0 ≤ estimate k c := by unfold estimate; positivity
  have hnk' : n * k ≤ 16 ^ k := by
    calc n * k ≤ 2 ^ k * 8 ^ k :=
          Nat.mul_le_mul hnk ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by norm_num) k))
      _ = 16 ^ k := by rw [← mul_pow]; norm_num
  have h4 : 4 ≤ 16 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  have nlow : S ^ k ≤ 16 ^ k * 2 ^ c :=
    hlow.trans (Nat.mul_le_mul_right _ (hc.trans hnk'))
  have nup : 2 ^ c ≤ 16 ^ k * S ^ k := hup.trans (Nat.mul_le_mul_right _ h4)
  constructor
  · refine (pow_le_pow_iff_left₀ (by positivity) hx hk0).1 ?_
    rw [estimate_pow k c hk, div_pow]
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast (by rw [mul_comm]; exact nlow : S ^ k ≤ 2 ^ c * 16 ^ k)
  · refine (pow_le_pow_iff_left₀ hx (by positivity) hk0).1 ?_
    rw [estimate_pow k c hk, mul_pow]
    exact_mod_cast nup

end Auditable.Analysis.AfCounterDac

open Auditable.Interface.Pseudocode in
/-- PAPER: combined.tex:60-64 (the theorem after algo:pigeons, "Algorithm algo:pigeons
solves DAC"), with the factor `16` and `n ≥ 4` of stock.tex:129, 133.
Proof-side owner for `Auditable.afCounter_dac`; its statement is fixed by the proof charter. -/
theorem Auditable.Analysis.afCounter_dac_proof (hprior : Prior) {n : ℕ} (hn : 4 ≤ n) (F : CNF n) (hsat : 1 ≤ solCount F) : (solCount F : ℝ) / 16 ≤ estimate (copies n) (Program.afCounter F).val.chigh ∧ estimate (copies n) (Program.afCounter F).val.chigh ≤ 16 * (solCount F : ℝ) := by
  rw [Auditable.afCounter_val_eq_result]
  have hk : 1 ≤ copies n := Nat.clog_pos (by norm_num) (by omega)
  have hS' : solCount (formulaCopies F) = solCount F ^ copies n :=
    solCount_makeCopies F (copies n)
  have hN : 1 ≤ nPrime n := Nat.mul_pos (by omega) hk
  obtain ⟨hc, hlow, hup⟩ := AfCounterDac.stockResult_bounds hN (formulaCopies F)
    (by rw [hS']; exact Nat.one_le_pow _ _ hsat)
  rw [hS'] at hlow hup
  exact AfCounterDac.dac_arith n (copies n) (solCount F) _ hk (Nat.le_pow_clog (by norm_num) n)
    hc hlow hup

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · via cl:stockup + lm:stockexist on the stock loop and `solCount_makeCopies`; no gap fact needed
-/
