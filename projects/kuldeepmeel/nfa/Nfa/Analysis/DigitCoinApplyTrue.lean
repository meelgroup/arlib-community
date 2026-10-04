import Nfa.Interface.Pseudocode

/-!
# The digit coin is a Bernoulli coin

`digitCoin_apply_true`: `Pseudocode.digitCoin p` (the digit rule applied to one
Geometric(1/2) index, the coin `reduce` uses) is heads with probability exactly `p`
for `p ∈ [0, 1]`.  For `p < 1` the `(k+1)`-st binary digit of `p` is read with
probability `2^{-(k+1)}`, and those digits sum to `p`.
-/

open scoped ENNReal
open Filter Topology


namespace Nfa.Analysis.DigitCoinAux

/-- `P(k) = 2^{-(k+1)}` for the tape's Geometric(1/2) index.

INTERNAL: the law of one cell of randomness.
TEXLINE: algorithm.tex:52 -/
theorem coinIndex_apply (k : ℕ) : Nfa.Run.coinIndex k = ENNReal.ofReal ((1 / 2) ^ (k + 1)) := by
  unfold Nfa.Run.coinIndex
  rw [MeasureTheory.Measure.toPMF_apply, ProbabilityTheory.geometricMeasure_singleton (by
    intro h; have := congrArg Subtype.val h; norm_num at this)]
  congr 1
  change (1 - (2⁻¹ : ℝ)) ^ k * 2⁻¹ = (1 / 2) ^ (k + 1)
  rw [pow_succ]; norm_num

/-- The binary digit `d_k` of `p`, as `0/1`.

INTERNAL: binary expansion.
TEXLINE: algorithm.tex:52 -/
noncomputable def bit (p : ℝ) (k : ℕ) : ℝ := if ⌊p * 2 ^ (k + 1)⌋ % 2 = 1 then 1 else 0

/-- `⌊2x⌋ = 2⌊x⌋ + (⌊2x⌋ mod 2)`.

INTERNAL: one step of the binary expansion.
TEXLINE: algorithm.tex:52 -/
theorem floor_two_mul (x : ℝ) : ⌊2 * x⌋ = 2 * ⌊x⌋ + ⌊2 * x⌋ % 2 := by
  have h1 : 2 * ⌊x⌋ ≤ ⌊2 * x⌋ := by
    rw [Int.le_floor]; push_cast; linarith [Int.floor_le x]
  have h2 : ⌊2 * x⌋ < 2 * ⌊x⌋ + 2 := by
    rw [Int.floor_lt]; push_cast; linarith [Int.lt_floor_add_one x]
  omega

/-- The first `K` binary digits of `p ∈ [0,1)` sum to `⌊p·2^K⌋/2^K`.

INTERNAL: binary expansion.
TEXLINE: algorithm.tex:52 -/
theorem partial_sum (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) : ∀ K : ℕ,
    ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ (k + 1) * bit p k = ⌊p * 2 ^ K⌋ / 2 ^ K
  | 0 => by
      have : ⌊p⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hp0, hp1⟩
      simp [this]
  | K + 1 => by
      rw [Finset.sum_range_succ, partial_sum p hp0 hp1 K, one_div_pow]
      have h := floor_two_mul (p * 2 ^ K)
      rw [show 2 * (p * 2 ^ K) = p * 2 ^ (K + 1) by ring] at h
      unfold bit
      have hmod : ⌊p * 2 ^ (K + 1)⌋ % 2 = 0 ∨ ⌊p * 2 ^ (K + 1)⌋ % 2 = 1 := by omega
      rcases hmod with h0 | h1
      · rw [h0] at h
        rw [if_neg (by omega), h]
        push_cast
        field_simp
        ring
      · rw [h1] at h
        rw [if_pos h1, h]
        push_cast
        field_simp
        ring


/-- Digits are nonnegative.

INTERNAL: binary expansion.
TEXLINE: algorithm.tex:52 -/
theorem bit_nonneg (p : ℝ) (k : ℕ) : 0 ≤ bit p k := by
  unfold bit; split_ifs <;> norm_num

/-- `Σ_k 2^{-(k+1)} d_k(p) = p` for `p ∈ [0,1)`.

INTERNAL: binary expansion.
TEXLINE: algorithm.tex:52 -/
theorem hasSum_bits (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasSum (fun k => (1 / 2 : ℝ) ^ (k + 1) * bit p k) p := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => mul_nonneg (by positivity) (bit_nonneg p k))]
  simp_rw [partial_sum p hp0 hp1]
  have hlo : ∀ K : ℕ, p - (1 / 2) ^ K ≤ (⌊p * 2 ^ K⌋ : ℝ) / 2 ^ K := by
    intro K
    have h2 : (0 : ℝ) < 2 ^ K := by positivity
    rw [le_div_iff₀ h2, one_div_pow, sub_mul, div_mul_cancel₀ _ h2.ne']
    linarith [Int.lt_floor_add_one (p * 2 ^ K)]
  have hhi : ∀ K : ℕ, (⌊p * 2 ^ K⌋ : ℝ) / 2 ^ K ≤ p := by
    intro K
    have h2 : (0 : ℝ) < 2 ^ K := by positivity
    rw [div_le_iff₀ h2]
    exact Int.floor_le _
  have hlim : Tendsto (fun K : ℕ => p - (1 / 2 : ℝ) ^ K) atTop (𝓝 p) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_sub p
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlo hhi

end Nfa.Analysis.DigitCoinAux

namespace Nfa.Analysis

open DigitCoinAux

/-- **`reduce`'s coin is Bernoulli(`p`)**: the digit rule on a Geometric(1/2) index
comes up heads with probability exactly `p`, for `p ∈ [0, 1]`.

PAPER: algorithm.tex:49-56 (`reduce(S, p)` adds each element with probability `p`;
the tape realises that coin by the digit rule, `Model/Run.lean`). -/
theorem digitCoin_apply_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Nfa.Pseudocode.digitCoin p true = ENNReal.ofReal p := by
  unfold Nfa.Pseudocode.digitCoin
  rw [PMF.map_apply]
  rcases hp1.lt_or_eq with hp1 | rfl
  · have hterm : ∀ k, (@ite _ (true = Nfa.Pseudocode.digit k p) (Classical.propDecidable _)
        (Nfa.Run.coinIndex k) 0) =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1) * bit p k) := by
      intro k
      unfold Nfa.Pseudocode.digit bit
      rw [if_neg (not_le.2 hp1), coinIndex_apply]
      by_cases h : ⌊p * 2 ^ (k + 1)⌋ % 2 = 1
      · simp [h]
      · simp [h]
    refine (tsum_congr hterm).trans ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun k => mul_nonneg (by positivity) (bit_nonneg p k)) (hasSum_bits p hp0 hp1).summable,
      (hasSum_bits p hp0 hp1).tsum_eq]
  · have hterm : ∀ k, (@ite _ (true = Nfa.Pseudocode.digit k 1) (Classical.propDecidable _)
        (Nfa.Run.coinIndex k) 0) =
        Nfa.Run.coinIndex k := by
      intro k
      unfold Nfa.Pseudocode.digit
      simp
    refine (tsum_congr hterm).trans ?_
    rw [PMF.tsum_coe, ENNReal.ofReal_one]

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `digitCoin_apply_true` by the binary expansion of `p`
-/
