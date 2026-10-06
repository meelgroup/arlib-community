import Auditable.Model.Prior
import Auditable.Model.Prelude
import Mathlib.Data.FinEnum
import Auditable.Analysis.CellHashIndep
import Auditable.Analysis.BellareRompelTail

/-!
# A balanced hash exists at the right round (thm:intermediate, existence half)

The probabilistic-method half of the proof of thm:intermediate (bgp.tex:153-190):
at a round `m` where the expected cell load `μ = |sol F| / 2^m` lies in
`[4096 n, 8192 n)`, some coefficient vector `c ∈ H(n, m, n)` puts between
`ℓ = 1024 n` and `u = 16384 n` solutions into every cell `α ∈ {0,1}^m`.

The round `m₀ = ⌊log |sol F| − 12 − log n⌋` of the paper is chosen by the caller
(`Auditable/Analysis/TheoremEqualCellsDacProof.lean`), which turns
`8192 n ≤ |sol F|` into the two load bounds below and `m ≤ n`.

The paper's route: for `c` uniform over `Fin n → K`, the values of
`∑ⱼ cⱼ xʲ` at `n` distinct points are independent and uniform (Vandermonde), and
keeping the first `m` bits preserves uniformity, so the indicators
`[h(y) = α]`, `y ∈ sol F`, are `n`-wise independent with mean `μ`. The tail
bound of Bellare–Rompel (prelim.tex:132-143, cited as [BR1994], stated for an even
`t ≥ 4`, so take `t = n` or `t = n - 1`) with `ε = 1/2` bounds each cell's failure
probability by `8 · (4(tμ + t²)/μ²)^{t/2} ≤ 8 · 1000^{-t/2}`; a union bound over the
`2^m ≤ 2^n / (4096 n)` cells is `< 1`. `|Cnt − μ| < μ/2` gives `ℓ ≤ Cnt ≤ u`.

The Lean proof follows it: `n`-wise independence of `CellHash` is `cellHash_indep`
(`CellHashIndep.lean`); the tail bound is `bellareRompel_tail`
(`BellareRompelTail.lean`, the cited result, carried rather than proved) at
`t = 2 ⌊n/2⌋` and `ε = 1/2`, where `4(tμ + t²)/μ² ≤ 1/1000`; the union bound uses
only `2^m ≤ 2^n ≤ 2 · 4^{⌊n/2⌋}`, so `2^m · 8 · 1000^{-⌊n/2⌋} ≤ 16 · (4/1000)^2 < 1`.
-/

set_option autoImplicit false

open Finset

namespace Auditable.Analysis

/-- **Existence of a balanced `H(n, m, n)` hash** at a round whose expected cell load
`|sol F| / 2^m` lies in `[4096 n, 8192 n)`.

PAPER: bgp.tex:153-190 (the existence half of the proof of thm:intermediate, at the
paper's round `m = ⌊log |sol F| − 12 − log n⌋`, where `μ_m ∈ [4096n, 8192n]`). -/
theorem cellsExist_at (hprior : Prior) {K : Type} [Field K] [FinEnum K] {n : ℕ}
    (bits : K ≃ (Fin n → Bool)) (hn : 4 ≤ n) (F : CNF n) (m : ℕ) (hm : m ≤ n)
    (hlow : 4096 * n * 2 ^ m ≤ solCount F) (hhigh : solCount F < 8192 * n * 2 ^ m) :
    ∃ c : CellHash K n, cellsWith bits F (cellsLow n) (cellsHigh n) m c := by
  -- the moment order: the largest even `t ≤ n`
  set t := 2 * (n / 2) with ht
  have ht4 : 4 ≤ t := by omega
  have htn : t ≤ n := by omega
  have htev : Even t := ⟨n / 2, by omega⟩
  have ht2 : t / 2 = n / 2 := by omega
  set S : ℕ := solCount F with hS
  set p : ℝ := ((2 : ℝ) ^ m)⁻¹ with hp
  set μ : ℝ := (sol F).card * p with hμdef
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hμlo : 4096 * (n : ℝ) ≤ μ := by
    have : (4096 * n * 2 ^ m : ℝ) ≤ S := by exact_mod_cast hlow
    rw [hμdef, hp, ← div_eq_mul_inv, le_div_iff₀ h2m]
    simpa [hS, solCount] using this
  have hμhi : μ < 8192 * (n : ℝ) := by
    have : (S : ℝ) < 8192 * n * 2 ^ m := by exact_mod_cast hhigh
    rw [hμdef, hp, ← div_eq_mul_inv, div_lt_iff₀ h2m]
    simpa [hS, solCount] using this
  have hμpos : 0 < μ := by linarith
  -- the per-cell tail bound
  set q : ℝ := (t * μ + t ^ 2) / ((1 / 2) ^ 2 * μ ^ 2) with hq
  have hbad : ∀ α : Fin m → Bool,
      ((univ.filter fun c : CellHash K n =>
          (1 / 2) * μ ≤ |(cellCount bits F c m α : ℝ) - μ|).card : ℝ) ≤
        Fintype.card (CellHash K n) * (8 * q ^ (t / 2)) := by
    intro α
    have hind : ∀ T ⊆ sol F, T.card ≤ t →
        ((univ.filter fun c : CellHash K n =>
            ∀ y ∈ T, decide (CellHash.apply bits c m y = α) = true).card : ℝ) =
          Fintype.card (CellHash K n) * p ^ T.card := by
      intro T _ hTt
      have h := cellHash_indep bits m hm α T (hTt.trans htn)
      have h' : ((univ.filter fun c : CellHash K n =>
            ∀ y ∈ T, CellHash.apply bits c m y = α).card : ℝ) * ((2 : ℝ) ^ m) ^ T.card =
          Fintype.card (CellHash K n) := by exact_mod_cast h
      simp only [decide_eq_true_eq]
      rw [hp, inv_pow, ← h', mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
    have := bellareRompel_tail (Ω := CellHash K n) hprior (sol F)
      (fun y c => decide (CellHash.apply bits c m y = α)) p t ht4 htev ?_ ?_
      (1 / 2) (by norm_num)
    · simpa [cellCount, hμdef, hq] using this
    · intro T hT hTt
      rw [← hind T hT hTt]
      congr 2
      ext c
      simp
    · exact hμpos
  -- `q ≤ 1/1000`
  have hq1 : q ≤ 1 / 1000 := by
    have htR : (t : ℝ) ≤ n := by exact_mod_cast htn
    have ht0 : (0 : ℝ) ≤ t := by positivity
    rw [hq, div_le_iff₀ (by positivity)]
    have h1 : (t : ℝ) * μ ≤ μ ^ 2 / 4096 := by nlinarith
    have h2 : (t : ℝ) ^ 2 ≤ μ ^ 2 / 4096 ^ 2 := by
      have : (t : ℝ) ≤ μ / 4096 := by linarith
      calc (t : ℝ) ^ 2 ≤ (μ / 4096) ^ 2 := by gcongr
        _ = μ ^ 2 / 4096 ^ 2 := by ring
    nlinarith
  -- the union bound is below one
  have hunion : (2 : ℝ) ^ m * (8 * q ^ (t / 2)) < 1 := by
    have hq0 : 0 ≤ q := by rw [hq]; positivity
    have hk : 2 ≤ n / 2 := by omega
    have hpow : q ^ (t / 2) ≤ (1 / 1000) ^ (n / 2) := by
      rw [ht2]; exact pow_le_pow_left₀ hq0 hq1 _
    have h2n : (2 : ℝ) ^ m ≤ 2 * 4 ^ (n / 2) := by
      calc (2 : ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hm
        _ ≤ 2 ^ (2 * (n / 2) + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 2 * 4 ^ (n / 2) := by rw [pow_succ, pow_mul]; norm_num; ring
    calc (2 : ℝ) ^ m * (8 * q ^ (t / 2))
        ≤ (2 * 4 ^ (n / 2)) * (8 * (1 / 1000) ^ (n / 2)) := by gcongr
      _ = 16 * (4 / 1000) ^ (n / 2) := by rw [div_pow, div_pow, one_pow]; ring
      _ ≤ 16 * (4 / 1000) ^ 2 := by
          have := pow_le_pow_of_le_one (a := (4 / 1000 : ℝ)) (by norm_num) (by norm_num) hk
          linarith
      _ < 1 := by norm_num
  -- a coefficient vector outside every bad set
  by_contra hno
  simp only [not_exists] at hno
  have hsub : (univ : Finset (CellHash K n)) ⊆ univ.biUnion fun α : Fin m → Bool =>
      univ.filter fun c : CellHash K n => (1 / 2) * μ ≤ |(cellCount bits F c m α : ℝ) - μ| := by
    intro c _
    have hc := hno c
    simp only [cellsWith, not_forall, not_and_or, not_le] at hc
    obtain ⟨α, hα⟩ := hc
    simp only [mem_biUnion, mem_univ, mem_filter, true_and]
    refine ⟨α, ?_⟩
    rcases hα with hα | hα
    · have : (cellCount bits F c m α : ℝ) < 1024 * n := by
        simpa [cellsLow] using (show (cellCount bits F c m α : ℝ) < (cellsLow n : ℕ) by
          exact_mod_cast hα)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have : (16384 * n : ℝ) < cellCount bits F c m α := by
        simpa [cellsHigh] using (show ((cellsHigh n : ℕ) : ℝ) < cellCount bits F c m α by
          exact_mod_cast hα)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hcard := Finset.card_le_card hsub
  have hcardR : (Fintype.card (CellHash K n) : ℝ) ≤
      ∑ α : Fin m → Bool, ((univ.filter fun c : CellHash K n =>
        (1 / 2) * μ ≤ |(cellCount bits F c m α : ℝ) - μ|).card : ℝ) := by
    have := hcard.trans Finset.card_biUnion_le
    rw [Finset.card_univ] at this
    exact_mod_cast this
  have hsum := Finset.sum_le_sum fun α (_ : α ∈ (univ : Finset (Fin m → Bool))) => hbad α
  rw [Finset.sum_const, Finset.card_univ] at hsum
  have hΩ : (0 : ℝ) < Fintype.card (CellHash K n) := by exact_mod_cast Fintype.card_pos
  have hcm : (Fintype.card (Fin m → Bool) : ℝ) = 2 ^ m := by simp
  rw [nsmul_eq_mul, hcm] at hsum
  nlinarith

end Auditable.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `cellsExist_at` from `cellHash_indep`, `bellareRompel_tail` (t = 2⌊n/2⌋, ε = 1/2) and a union bound
* r1 · stated · `cellsExist_at` split off `equalCells_dac_proof` as the probabilistic core
-/
