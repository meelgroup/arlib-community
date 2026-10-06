import Auditable.Model.Prior
import Auditable.Model.Run
import Auditable.Meta.ModelClosure
import Auditable.Interface.Encoding
import Auditable.Interface.Pseudocode
import Auditable.Interface.ProgramModel
import Auditable.Analysis.SolCountMakeCopies
import Auditable.Analysis.HolesNecessary
import Auditable.Analysis.StockNecessary

/-!
# Soundness of `CountAuditor` (thm:finalaudit, the accuracy half)

If `CountAuditor(F, K)` returns `Verified` on an arbitrary certificate `K`, then
`|sol F| / 4 ≤ 2^{c_high / k} ≤ 16 · |sol F|` with `k = copies n = ⌈log₂ n⌉`.

The argument is finalaudit.tex:82-109. The verdict gives `φ_stock(c_high)`,
`φ_holes(c_low)` and `c_high ≤ c_low + 7`; lem:holes (`holes_necessary`) and
cl:stockup (`stock_necessary`) give
`2^{c_low} ≤ (c_low + 1) · |sol F'|` and `|sol F'| ≤ c_high · 2^{c_high}` (eq:imp), and
`|sol F'| = |sol F|^k` (`solCount_makeCopies`).

**Departure from the paper.** The paper assumes `c_low, c_high ≤ n log n`, which holds
for the honest certificate but not for an adversarial one. Here it is derived:
`|sol F'| ≤ 2^{nk}` and eq:imp force `c_low + 1 ≤ 2nk ≤ 2k · 2^k`
(`clow_bound`). The constants then close with `256 k · 2^k ≤ 16^k` and
`2k · 2^k + 7 ≤ 4^k` for `k ≥ 4`, which is where `12 ≤ n` (so `k ≥ 4`) is used, and
`n ≤ 2^k` (ceiling `log`) replaces the paper's `n^2 = 2^{2 log n}`.

The verdict is read through `Auditable.countAuditor_val_eq_verdict`
(`Interface/ProgramModel.lean`), the rung of the program/pseudocode ladder that holds
for every certificate.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable

/-- INTERNAL: `2d + 1 < 2^d` for `d ≥ 3`. -/
theorem two_mul_add_one_lt_two_pow {d : ℕ} (hd : 3 ≤ d) : 2 * d + 1 < 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih => rw [pow_succ]; omega

/-- INTERNAL: `256 k ≤ 8^k` for `k ≥ 4`. -/
theorem mul_256_le_eight_pow {k : ℕ} (hk : 4 ≤ k) : 256 * k ≤ 8 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

/-- INTERNAL: the bound on `c_low` the paper takes for granted (`c_low ≤ n log n`,
finalaudit.tex:93), derived from `2^l ≤ (l + 1) · 2^a` with `a ≥ 3`: `l + 1 ≤ 2a`.
TEXLINE: finalaudit.tex:91-95 -/
theorem clow_bound {l a T : ℕ} (ha : 3 ≤ a) (hT : T ≤ 2 ^ a) (h : 2 ^ l ≤ (l + 1) * T) :
    l + 1 ≤ 2 * a := by
  by_contra hlt
  replace hlt : 2 * a < l + 1 := Nat.lt_of_not_le hlt
  obtain ⟨d, rfl⟩ : ∃ d, l = a + d := ⟨l - a, by omega⟩
  have hda : a ≤ d := by omega
  have h1 : 2 ^ a * 2 ^ d ≤ 2 ^ a * (a + d + 1) := by
    rw [← pow_add, mul_comm (2 ^ a)]
    exact h.trans (Nat.mul_le_mul_left _ hT)
  have h2 : 2 ^ d ≤ a + d + 1 := Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 := two_mul_add_one_lt_two_pow (le_trans ha hda)
  omega

/-- INTERNAL: the natural-number core of finalaudit.tex:84-105. From eq:imp with
`|sol F'| = S^k`, the gap test, `S ≤ 2^n`, `n ≤ 2^k` and `k ≥ 4`:
`2^c ≤ (16 S)^k` and `S^k ≤ 4^k · 2^c`.
TEXLINE: finalaudit.tex:82-109 -/
theorem sound_nat {n S k l c : ℕ} (hn : 1 ≤ n) (hk : 4 ≤ k) (hnk : n ≤ 2 ^ k)
    (hS : S ≤ 2 ^ n) (hholes : 2 ^ l ≤ (l + 1) * S ^ k) (hstock : S ^ k ≤ c * 2 ^ c)
    (hgap : c ≤ l + 7) : 2 ^ c ≤ (16 * S) ^ k ∧ S ^ k ≤ 4 ^ k * 2 ^ c := by
  have hSk : S ^ k ≤ 2 ^ (n * k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hS k
  have ha : 3 ≤ n * k := by nlinarith
  have hl := clow_bound ha hSk hholes
  have hnk' : n * k ≤ k * 2 ^ k := by rw [mul_comm]; exact Nat.mul_le_mul_left k hnk
  have h2k : 16 ≤ 2 ^ k := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  constructor
  · have h8 := mul_256_le_eight_pow hk
    have h16 : (16 : ℕ) ^ k = 8 ^ k * 2 ^ k := by
      rw [← mul_pow]; norm_num
    calc 2 ^ c ≤ 2 ^ (l + 7) := Nat.pow_le_pow_right (by norm_num) hgap
      _ = 128 * 2 ^ l := by rw [pow_add]; ring
      _ ≤ 128 * ((l + 1) * S ^ k) := Nat.mul_le_mul_left _ hholes
      _ ≤ 128 * ((2 * (k * 2 ^ k)) * S ^ k) := by
          gcongr; omega
      _ = (256 * k) * 2 ^ k * S ^ k := by ring
      _ ≤ 8 ^ k * 2 ^ k * S ^ k := by gcongr
      _ = (16 * S) ^ k := by rw [mul_pow, h16]
  · have h3 := two_mul_add_one_lt_two_pow (show 3 ≤ k by omega)
    have hc : c ≤ 4 ^ k := by
      have h4 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
      have : 2 * (k * 2 ^ k) + 7 ≤ 2 ^ k * 2 ^ k := by
        nlinarith
      omega
    calc S ^ k ≤ c * 2 ^ c := hstock
      _ ≤ 4 ^ k * 2 ^ c := Nat.mul_le_mul_right _ hc

/-- PAPER: finalaudit.tex:82-109 (proof of thm:finalaudit, soundness part): if the auditor
returns `Verified` on a certificate `K`, then `|sol F| / 4 ≤ CntEst ≤ 16 · |sol F|` with
`CntEst = 2^{c_high / log n}`. -/
theorem finalAudit_sound_proof (hprior : Prior) {n : ℕ} (hn : 12 ≤ n) (F : CNF n) (K : Cert (nPrime n)) (hK : (Program.countAuditor F K).val = Verdict.verified) : (solCount F : ℝ) / 4 ≤ estimate (copies n) K.chigh ∧ estimate (copies n) K.chigh ≤ 16 * (solCount F : ℝ) := by
  rw [Auditable.countAuditor_val_eq_verdict] at hK
  unfold Interface.Pseudocode.verdict at hK
  split_ifs at hK with h
  obtain ⟨⟨hpos, hneg⟩, hgap⟩ := h
  set k := copies n with hkdef
  set S := solCount F with hSdef
  have hcopies : solCount (Interface.Pseudocode.formulaCopies F) = S ^ k :=
    solCount_makeCopies F (copies n)
  have hholes := holes_necessary _ _ _ hneg
  have hstock := stock_necessary _ _ _ hpos
  rw [hcopies] at hholes hstock
  have hk : 4 ≤ k := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by omega)
  have hnk : n ≤ 2 ^ k := Nat.le_pow_clog (by norm_num) n
  have hS : S ≤ 2 ^ n := by
    calc S = (sol F).card := rfl
      _ ≤ (Finset.univ : Finset (Assignment n)).card := Finset.card_le_univ _
      _ = 2 ^ n := by simp
  obtain ⟨hup, hlow⟩ := sound_nat (by omega) hk hnk hS hholes hstock hgap
  have hk0 : k ≠ 0 := by omega
  have hE0 : 0 ≤ estimate k K.chigh := by unfold estimate; positivity
  have hEk : estimate k K.chigh ^ k = (2 : ℝ) ^ K.chigh := by
    unfold estimate
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ (by exact_mod_cast hk0),
      Real.rpow_natCast]
  constructor
  · refine (pow_le_pow_iff_left₀ (by positivity) hE0 hk0).1 ?_
    rw [hEk, div_pow, div_le_iff₀ (by positivity)]
    calc (S : ℝ) ^ k ≤ (4 : ℝ) ^ k * 2 ^ K.chigh := by exact_mod_cast hlow
      _ = 2 ^ K.chigh * 4 ^ k := mul_comm _ _
  · refine (pow_le_pow_iff_left₀ hE0 (by positivity) hk0).1 ?_
    rw [hEk]
    exact_mod_cast hup

end Auditable.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `finalAudit_sound_proof` via `countAuditor_val_eq_verdict`, `holes_necessary`, `stock_necessary`, `solCount_makeCopies`; `c_low` bound derived (`clow_bound`)
-/
