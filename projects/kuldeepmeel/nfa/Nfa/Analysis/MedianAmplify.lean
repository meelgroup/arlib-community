import Nfa.Interface.Pseudocode
import Arlib.Probability.Median

/-!
# Median amplification

`median_amplify`: if one draw from `ν` lands outside `[lo, hi]` with probability at
most `1/4`, the median (`Arlib.Probability.medianOf`, the `⌊μ/2⌋`-th order
statistic) of `μ` independent draws (`Pseudocode.drawAll` over `List.range μ`)
lands outside with probability at most `exp(−μ/8)`.  This is the amplification
step of the main theorem's proof (analysis.tex:61-66).

The paper invokes Hoeffding's bound.  Here the tail is proved directly, with no
borrowed result: a median outside `[lo, hi]` forces at least `μ/2` failing draws
(`Arlib.Probability.median_mem_Icc_of_lt_half_outside`); `E[4^{X̄}] ≤ (7/4)^μ` by
independence (`mgf_drawAll`); Markov gives `P(X̄ ≥ μ/2) ≤ (7/8)^μ ≤ exp(−μ/8)`.
-/

open scoped ENNReal

namespace Nfa.Analysis.MedianAmplifyAux

open Classical

/-- Expectation under a pushforward PMF.

INTERNAL: PMF bookkeeping for the median-amplification tail bound.
TEXLINE: analysis.tex:63-65 -/
theorem tsum_map_mul {α β : Type} (p : PMF α) (f : α → β) (h : β → ℝ≥0∞) :
    ∑' b, p.map f b * h b = ∑' a, p a * h (f a) := by
  classical
  simp only [PMF.map_apply]
  calc ∑' b, (∑' a, if b = f a then p a else 0) * h b
      = ∑' b, ∑' a, (if b = f a then p a * h (f a) else 0) := by
        refine tsum_congr fun b => ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun a => ?_
        split_ifs with hb
        · rw [hb]
        · simp
    _ = ∑' a, ∑' b, (if b = f a then p a * h (f a) else 0) := ENNReal.tsum_comm
    _ = ∑' a, p a * h (f a) := tsum_congr fun a => tsum_ite_eq (f a) _

/-- Expectation under a bound PMF.

INTERNAL: PMF bookkeeping for the median-amplification tail bound.
TEXLINE: analysis.tex:63-65 -/
theorem tsum_bind_mul {α β : Type} (p : PMF α) (q : α → PMF β) (h : β → ℝ≥0∞) :
    ∑' b, p.bind q b * h b = ∑' a, p a * ∑' b, q a b * h b := by
  simp only [PMF.bind_apply]
  calc ∑' b, (∑' a, p a * q a b) * h b = ∑' b, ∑' a, p a * (q a b * h b) := by
        refine tsum_congr fun b => ?_
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun a => mul_assoc _ _ _
    _ = ∑' a, ∑' b, p a * (q a b * h b) := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, q a b * h b := tsum_congr fun a => ENNReal.tsum_mul_left

/-- Markov's inequality for a PMF, in `ℝ≥0∞`: if `h ≥ t` on `s` then `t · P(s) ≤ E[h]`.

INTERNAL: the Markov step of the median-amplification tail bound.
TEXLINE: analysis.tex:63-65 -/
theorem mul_toOuterMeasure_le {α : Type} (p : PMF α) (s : Set α) (t : ℝ≥0∞) (h : α → ℝ≥0∞)
    (hs : ∀ x ∈ s, t ≤ h x) : t * p.toOuterMeasure s ≤ ∑' x, p x * h x := by
  rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, mul_comm]
    exact mul_le_mul_right (hs x hx) _
  · rw [Set.indicator_of_notMem hx, mul_zero]
    exact zero_le


/-- The number of listed indices whose draw falls in `E` (the paper's `X̄`).

INTERNAL: the failure count `X̄ = X_1 + ⋯ + X_μ` of analysis.tex:63.
TEXLINE: analysis.tex:63 -/
noncomputable def failCount (E : Set ℝ) (L : List ℕ) (g : ℕ → ℝ) : ℕ := by
  classical exact L.countP fun j => decide (g j ∈ E)

/-- Updating a fresh index adds that draw's own failure indicator.

INTERNAL: the inductive step of the moment bound.
TEXLINE: analysis.tex:63-65 -/
theorem failCount_cons_update (E : Set ℝ) (i : ℕ) (is : List ℕ) (hi : i ∉ is) (g : ℕ → ℝ)
    (b : ℝ) : (4 : ℝ≥0∞) ^ failCount E (i :: is) (Function.update g i b) =
      (if b ∈ E then 4 else 1) * 4 ^ failCount E is g := by
  classical
  unfold failCount
  rw [List.countP_cons]
  have hcongr : is.countP (fun j => decide (Function.update g i b j ∈ E)) =
      is.countP (fun j => decide (g j ∈ E)) := by
    refine List.countP_congr fun j hj => ?_
    have : j ≠ i := fun h => hi (h ▸ hj)
    simp [Function.update_of_ne this]
  rw [hcongr, pow_add, mul_comm]
  congr 1
  by_cases hb : b ∈ E <;> simp [hb]

/-- One draw contributes a factor `E[4^{X_i}] = 1 + 3·P(fail) ≤ 7/4`.

INTERNAL: the per-coordinate moment factor.
TEXLINE: analysis.tex:63-65 -/
theorem factor_le (ν : PMF ℝ) (E : Set ℝ) (hE : ν.toOuterMeasure E ≤ 1 / 4) :
    ∑' b, ν b * (if b ∈ E then (4 : ℝ≥0∞) else 1) ≤ 7 / 4 := by
  classical
  have hsplit : ∀ b, ν b * (if b ∈ E then (4 : ℝ≥0∞) else 1) = ν b + 3 * E.indicator ν b := by
    intro b
    by_cases hb : b ∈ E
    · rw [if_pos hb, Set.indicator_of_mem hb]; ring
    · rw [if_neg hb, Set.indicator_of_notMem hb]; ring
  rw [tsum_congr hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_left, PMF.tsum_coe,
    ← PMF.toOuterMeasure_apply]
  calc 1 + 3 * ν.toOuterMeasure E ≤ 1 + 3 * (1 / 4) := by gcongr
    _ = 7 / 4 := by
      rw [mul_one_div, show (7:ℝ≥0∞) = 4 + 3 by norm_num, ← ENNReal.div_add_div_same,
        ENNReal.div_self (by norm_num) (by norm_num)]

/-- **Moment bound**: `E[4^{X̄}] ≤ (7/4)^{|L|}` for independent draws over a duplicate-free list.

INTERNAL: replaces the paper's appeal to Hoeffding's bound.
TEXLINE: analysis.tex:63-65 -/
theorem mgf_drawAll (ν : PMF ℝ) (E : Set ℝ) (hE : ν.toOuterMeasure E ≤ 1 / 4) :
    ∀ L : List ℕ, L.Nodup →
      ∑' g, Nfa.Pseudocode.drawAll (fun _ => ν) 0 L g * 4 ^ failCount E L g ≤ (7 / 4) ^ L.length
  | [], _ => by
      simp only [Nfa.Pseudocode.drawAll, failCount, List.countP_nil, pow_zero, mul_one,
        PMF.tsum_coe, List.length_nil, le_refl]
  | i :: is, hL => by
      rw [List.nodup_cons] at hL
      have ih := mgf_drawAll ν E hE is hL.2
      simp only [Nfa.Pseudocode.drawAll]
      rw [tsum_bind_mul]
      simp only [tsum_map_mul, failCount_cons_update E i is hL.1]
      calc ∑' b, ν b * ∑' g, Nfa.Pseudocode.drawAll (fun _ => ν) 0 is g *
              ((if b ∈ E then 4 else 1) * 4 ^ failCount E is g)
          = ∑' b, ν b * (if b ∈ E then (4 : ℝ≥0∞) else 1) *
              ∑' g, Nfa.Pseudocode.drawAll (fun _ => ν) 0 is g * 4 ^ failCount E is g := by
            refine tsum_congr fun b => ?_
            rw [mul_assoc]
            congr 1
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun g => by ring
        _ = (∑' b, ν b * (if b ∈ E then (4 : ℝ≥0∞) else 1)) *
              ∑' g, Nfa.Pseudocode.drawAll (fun _ => ν) 0 is g * 4 ^ failCount E is g :=
            ENNReal.tsum_mul_right
        _ ≤ (7 / 4 : ℝ≥0∞) * (7 / 4) ^ is.length := by gcongr; exact factor_le ν E hE
        _ = (7 / 4) ^ (i :: is).length := by rw [List.length_cons, pow_succ, mul_comm]


/-- The failure count over `List.range μ` is the count over `Fin μ` that `Arlib`'s median lemma uses.

INTERNAL: index bookkeeping between `drawAll` and `medianOf`.
TEXLINE: analysis.tex:65 -/
theorem failCount_range (E : Set ℝ) (g : ℕ → ℝ) :
    ∀ μ, failCount E (List.range μ) g =
      (Finset.univ.filter fun b : Fin μ => g b ∈ E).card
  | 0 => by simp [failCount]
  | μ + 1 => by
      have ih := failCount_range E g μ
      unfold failCount at ih ⊢
      rw [List.range_succ, List.countP_append, ih, Finset.card_filter, Finset.card_filter,
        Fin.sum_univ_castSucc]
      simp

/-- `(7/4)^μ ≤ 2^μ · exp(−μ/8)`, i.e. `(7/8)^μ ≤ exp(−μ/8)`, from `exp(1/8) ≤ 8/7`.

INTERNAL: the numeric tail of the amplification bound.
TEXLINE: analysis.tex:65 -/
theorem seven_eighths_pow_le (μ : ℕ) :
    (7 / 4 : ℝ≥0∞) ^ μ ≤ 2 ^ μ * ENNReal.ofReal (Real.exp (-(μ : ℝ) / 8)) := by
  have hbase : (7 / 8 : ℝ) ≤ Real.exp (-1 / 8) := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 8) (by norm_num) (by norm_num)
    rw [show (-1 / 8 : ℝ) = -(1 / 8) by ring, Real.exp_neg]
    rw [show (1 : ℝ) / (1 - 1 / 8) = 8 / 7 by norm_num] at h
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    calc Real.exp (1 / 8) ≤ 8 / 7 := h
      _ = (7 / 8)⁻¹ := by norm_num
  have hreal : (7 / 4 : ℝ) ^ μ ≤ 2 ^ μ * Real.exp (-(μ : ℝ) / 8) := by
    rw [show (7 / 4 : ℝ) = 2 * (7 / 8) by norm_num, mul_pow,
      show -(μ : ℝ) / 8 = μ * (-1 / 8) by ring, Real.exp_nat_mul]
    gcongr
  calc (7 / 4 : ℝ≥0∞) ^ μ = ENNReal.ofReal ((7 / 4 : ℝ) ^ μ) := by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal (2 ^ μ * Real.exp (-(μ : ℝ) / 8)) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 ^ μ * ENNReal.ofReal (Real.exp (-(μ : ℝ) / 8)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        norm_num

end Nfa.Analysis.MedianAmplifyAux

namespace Nfa.Analysis

open MedianAmplifyAux

/-- **Median amplification** (analysis.tex:63-65): with failure probability at most
`1/4` per draw, the median of `μ` independent draws fails with probability at
most `exp(−μ/8)`.

PAPER: analysis.tex:63-65.  The paper cites Hoeffding's bound for this step; it is
proved here instead, by Markov on `4^{X̄}` with `E[4^{X̄}] ≤ (7/4)^μ`. -/
theorem median_amplify (ν : PMF ℝ) (lo hi : ℝ)
    (hfail : ν.toOuterMeasure (Set.Icc lo hi)ᶜ ≤ 1 / 4) (μ : ℕ) :
    ((Nfa.Pseudocode.drawAll (fun _ => ν) 0 (List.range μ)).map fun ests =>
        Arlib.Probability.medianOf fun j : Fin μ => ests j).toOuterMeasure (Set.Icc lo hi)ᶜ
      ≤ ENNReal.ofReal (Real.exp (-(μ : ℝ) / 8)) := by
  classical
  set D := Nfa.Pseudocode.drawAll (fun _ => ν) 0 (List.range μ)
  rw [PMF.toOuterMeasure_map_apply]
  have hmarkov := mul_toOuterMeasure_le D
    ((fun ests => Arlib.Probability.medianOf fun j : Fin μ => ests j) ⁻¹' (Set.Icc lo hi)ᶜ)
    (2 ^ μ) (fun g => 4 ^ failCount (Set.Icc lo hi)ᶜ (List.range μ) g) (by
      intro g hg
      have hout : ¬ 2 * (Finset.univ.filter fun b : Fin μ => g b ∉ Set.Icc lo hi).card < μ :=
        fun h => hg (Arlib.Probability.median_mem_Icc_of_lt_half_outside
          (Arlib.Probability.isMedian_medianOf _) h)
      have hcnt : μ ≤ 2 * failCount (Set.Icc lo hi)ᶜ (List.range μ) g := by
        rw [failCount_range]
        simpa using hout
      calc (2 : ℝ≥0∞) ^ μ ≤ 2 ^ (2 * failCount (Set.Icc lo hi)ᶜ (List.range μ) g) :=
            pow_le_pow_right₀ (by norm_num) hcnt
        _ = 4 ^ failCount (Set.Icc lo hi)ᶜ (List.range μ) g := by
            rw [pow_mul]; norm_num)
  have hmgf := mgf_drawAll ν _ hfail (List.range μ) List.nodup_range
  rw [List.length_range] at hmgf
  have h2 : (2 : ℝ≥0∞) ^ μ ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2' : (2 : ℝ≥0∞) ^ μ ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [← ENNReal.mul_le_mul_iff_right h2 h2']
  exact hmarkov.trans (hmgf.trans (seven_eighths_pow_le μ))

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `median_amplify` by Markov on `4^{X̄}`, `E[4^{X̄}] ≤ (7/4)^μ`, `exp(1/8) ≤ 8/7`
-/
