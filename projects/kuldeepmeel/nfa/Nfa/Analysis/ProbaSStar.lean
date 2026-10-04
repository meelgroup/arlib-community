import Nfa.Analysis.ProbaPStar
import Nfa.Analysis.AtomExpectationLe
import Mathlib.Data.Set.Finite.List

/-!
# Lemma proba_S(q): `countNFAcore*` rarely stores `θ` samples

`proba_S_star` is Lemma proba_S(q) (analysis.tex:10-13, proof analysis.tex:471-523):
in `countNFAcore*` with the paper's parameters, `Σ_{r ∈ [α], q ∈ Q^u} |S^r(q)| ≥ θ`
with probability at most `1/8`.

Proof (paper's): split on the event of `proba_p_star` (`≤ 1/16`).  Off it, every
`p(q) ≤ 1/((1−ε/2)|L(q)|)`, so by Markov
`Pr[Σ|S| ≥ θ ∧ all good] ≤ θ⁻¹ Σ_{r,q} E[|S^r(q)| 1_{good(q)}]
  ≤ θ⁻¹ Σ_{r,q} E[|S^r(q)|/p(q)] / ((1−ε/2)|L(q)|) = α|Q^u| / ((1−ε/2)θ) ≤ 1/16`,
using `E[|S^r(q)|/p(q)] ≤ |L(q)|` (`atom_expectation_le`, the `≤` half of
atoms_have_expected_value_one, analysis.tex:475-486, summed over words), `1/(1−ε/2) ≤ 1+ε`
and `θ ≥ 16α(1+ε)|Q^u|`.  The Markov half is `proba_S_star_markov`.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Nfa.Analysis

open Nfa.Pseudocode

variable {Q : Type} [Fintype Q] [LinearOrder Q]

omit [Fintype Q] [LinearOrder Q] in
/-- `L(q^ℓ)` is finite: its words all have length `ℓ`.

INTERNAL: finiteness behind `langCount` as a true cardinality.
TEXLINE: background.tex:18 -/
theorem langSet_finite (A : PaperNFA Q) (ℓ : ℕ) (q : Q) :
    {w : List Bool | w.length = ℓ ∧ q ∈ A.toNFA.eval w}.Finite :=
  (List.finite_length_eq Bool ℓ).subset fun _ hw => hw.1

omit [LinearOrder Q] in
/-- `|L(q^ℓ)| ≥ 1` for `q ∈ Q^ℓ`.

INTERNAL: makes the upper end of `goodWindow` a real bound on `p(q)`.
TEXLINE: background.tex:32 -/
theorem one_le_langCount (A : PaperNFA Q) (ℓ : ℕ) (q : Q) (hq : q ∈ layerSet A ℓ) :
    1 ≤ langCount A ℓ q := by
  classical
  have hq' : q ∈ A.layer ℓ := by simpa [layerSet] using hq
  obtain ⟨w, hw, hqw⟩ := hq'
  unfold langCount
  exact Nat.one_le_iff_ne_zero.2 <| (Set.ncard_pos (langSet_finite A ℓ q)).2 ⟨w, hw, hqw⟩ |>.ne'

omit [Fintype Q] [LinearOrder Q] in
/-- `Σ_w 1_{w ∈ L(q^ℓ)} = |L(q^ℓ)|` in `ℝ≥0∞`.

INTERNAL: the sum over `w ∈ L(q)` of analysis.tex:510-514.
TEXLINE: analysis.tex:510-514 -/
theorem tsum_langSet_indicator (A : PaperNFA Q) (ℓ : ℕ) (q : Q) :
    ∑' w, Set.indicator {w : List Bool | w.length = ℓ ∧ q ∈ A.toNFA.eval w} 1 w =
      (langCount A ℓ q : ℝ≥0∞) := by
  rw [← tsum_subtype]
  simp only [Pi.one_apply]
  rw [ENNReal.tsum_set_one, langCount,
    ← (langSet_finite A ℓ q).cast_ncard_eq]
  rfl

omit [LinearOrder Q] in
/-- `Σ_{ℓ ≤ n} |Q^ℓ| = |Q^u|`.

INTERNAL: matches `storedTotal`'s index set with `unrolledCard`.
TEXLINE: background.tex:32 -/
theorem sum_card_layerSet (A : PaperNFA Q) (n : ℕ) :
    ∑ ℓ ∈ Finset.range (n + 1), (layerSet A ℓ).card = A.unrolledCard n := by
  classical
  unfold PaperNFA.unrolledCard
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← Set.ncard_coe_finset]
  congr 1
  ext q
  simp [layerSet]

omit [LinearOrder Q] in
/-- `|Q^u| ≥ 1` (`q_I ∈ Q^0`).

INTERNAL: positivity of `γ` and `θ`.
TEXLINE: background.tex:32 -/
theorem one_le_unrolledCard (A : PaperNFA Q) (n : ℕ) : 1 ≤ A.unrolledCard n := by
  classical
  rw [← sum_card_layerSet]
  have h0 : A.qI ∈ layerSet A 0 := by
    simp only [layerSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨[], rfl, by simp [PaperNFA.toNFA]⟩
  calc 1 ≤ (layerSet A 0).card := Finset.card_pos.2 ⟨_, h0⟩
    _ ≤ _ := Finset.single_le_sum (f := fun ℓ => (layerSet A ℓ).card)
        (fun _ _ => Nat.zero_le _) (by simp)

omit [LinearOrder Q] in
/-- `α|Q^u|/(1−ε/2) ≤ θ/16` and `θ > 0`, from `θ = ⌈16α(1+ε)|Q^u|⌉` and
`1/(1−ε/2) ≤ 1+ε`.

INTERNAL: the parameter arithmetic closing analysis.tex:517-523.
TEXLINE: analysis.tex:517-523, algorithm.tex:92 -/
theorem params_theta_bound (A : PaperNFA Q) (n : ℕ) (ε δ : ℝ) (hn : 1 ≤ n) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ((Nfa.params A n ε δ).α : ℝ) * A.unrolledCard n * (1 / (1 - ε / 2)) ≤
        (Nfa.params A n ε δ).θ / 16 ∧ 0 < (Nfa.params A n ε δ).θ := by
  have hQu : (1 : ℝ) ≤ A.unrolledCard n := by exact_mod_cast one_le_unrolledCard A n
  have hβ : 1 ≤ ⌈64 * (n : ℝ) / (ε ^ 2 * (1 - ε))⌉₊ := by
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.ceil_pos]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 < 1 - ε := by linarith
    positivity
  have hγ : 1 ≤ ⌈5 * Real.log (16 * (A.unrolledCard n : ℝ))⌉₊ := by
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.ceil_pos]
    have : 0 < Real.log (16 * (A.unrolledCard n : ℝ)) := Real.log_pos (by linarith)
    linarith
  simp only [Nfa.params]
  set β := ⌈64 * (n : ℝ) / (ε ^ 2 * (1 - ε))⌉₊
  set γ := ⌈5 * Real.log (16 * (A.unrolledCard n : ℝ))⌉₊
  set Qu : ℝ := (A.unrolledCard n : ℝ)
  have hα : (1 : ℝ) ≤ ((β * γ : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hceil := Nat.le_ceil (16 * ((β * γ : ℕ) : ℝ) * (1 + ε) * Qu)
  have hinv : 1 / (1 - ε / 2) ≤ 1 + ε := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  constructor
  · calc ((β * γ : ℕ) : ℝ) * Qu * (1 / (1 - ε / 2)) ≤ ((β * γ : ℕ) : ℝ) * Qu * (1 + ε) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (16 * ((β * γ : ℕ) : ℝ) * (1 + ε) * Qu) / 16 := by ring
      _ ≤ _ := by gcongr
  · rw [Nat.ceil_pos]; positivity

/-- **The Markov half of proba_S(q)**: `Pr[Σ|S| ≥ θ ∧ every p(q) in its window] ≤ 1/16`.

INTERNAL: eq. markov_bound_for_number_of_sample with the `ε/2` window of `proba_p_star`.
TEXLINE: analysis.tex:493-523 -/
theorem proba_S_star_markov
    (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ)
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (coreLawStar A σ (Nfa.params A n ε δ) n).toOuterMeasure
      ({st | (Nfa.params A n ε δ).θ ≤ storedTotal A n (Nfa.params A n ε δ) st} ∩
        {st : CoreState Q | ∃ ℓ ≤ n, ∃ q ∈ layerSet A ℓ,
          st.p ℓ q ∉ goodWindow ε (langCount A ℓ q : ℝ)}ᶜ) ≤ 1 / 16 := by
  set P := Nfa.params A n ε δ
  set D := coreLawStar A σ P n
  set Over := {st : CoreState Q | P.θ ≤ storedTotal A n P st}
  set Bad := {st : CoreState Q |
    ∃ ℓ ≤ n, ∃ q ∈ layerSet A ℓ, st.p ℓ q ∉ goodWindow ε (langCount A ℓ q : ℝ)}
  set K : ℕ → Q → ℝ≥0∞ := fun ℓ q => ENNReal.ofReal (1 / ((1 - ε / 2) * (langCount A ℓ q : ℝ)))
  set F : CoreState Q → ℝ≥0∞ := fun st => ∑ ℓ ∈ Finset.range (n + 1), ∑ q ∈ layerSet A ℓ,
    ∑ r ∈ Finset.range P.α, K ℓ q * ∑' w, atomVal r ℓ q w st with hF
  have hpt : ∀ st, st ∉ Bad → (storedTotal A n P st : ℝ≥0∞) ≤ F st := by
    intro st hst
    simp only [Bad, Set.mem_setOf_eq, not_exists, not_and, not_not] at hst
    unfold storedTotal
    rw [hF]
    push_cast
    gcongr with ℓ hℓ q hq r hr
    have hL : (1 : ℝ) ≤ langCount A ℓ q := by exact_mod_cast one_le_langCount A ℓ q hq
    obtain ⟨hlo, hhi⟩ := hst ℓ (by simpa [Nat.lt_succ_iff] using hℓ) q hq
    have hp : 0 < st.p ℓ q := lt_of_lt_of_le (by
      have : 0 < 1 + ε / 2 := by linarith
      positivity) hlo
    have h1 : 1 ≤ K ℓ q * ENNReal.ofReal (1 / st.p ℓ q) := by
      have : 0 < 1 - ε / 2 := by linarith
      rw [← ENNReal.ofReal_mul (by positivity), ENNReal.one_le_ofReal, mul_one_div,
        le_div_iff₀ hp, one_mul]
      exact hhi
    calc ((st.S ℓ q r).card : ℝ≥0∞) = ∑ w ∈ st.S ℓ q r, (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ w ∈ st.S ℓ q r, K ℓ q * atomVal r ℓ q w st :=
          Finset.sum_le_sum fun w hw => by simpa [atomVal, hw] using h1
      _ ≤ ∑' w, K ℓ q * atomVal r ℓ q w st := ENNReal.sum_le_tsum _
      _ = K ℓ q * ∑' w, atomVal r ℓ q w st := ENNReal.tsum_mul_left
  have hEF : ∑' st, D st * F st ≤
      ((P.α * A.unrolledCard n : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - ε / 2)) := by
    calc ∑' st, D st * F st = ∑ ℓ ∈ Finset.range (n + 1), ∑ q ∈ layerSet A ℓ,
          ∑ r ∈ Finset.range P.α, K ℓ q * ∑' w, ∑' st, D st * atomVal r ℓ q w st := by
          simp only [hF, Finset.mul_sum]
          rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun w => tsum_congr fun st => ?_
          ring
      _ ≤ ∑ ℓ ∈ Finset.range (n + 1), ∑ q ∈ layerSet A ℓ,
          ∑ r ∈ Finset.range P.α, K ℓ q * (langCount A ℓ q : ℝ≥0∞) := by
          gcongr with ℓ _ q _ r _
          rw [← tsum_langSet_indicator]
          exact ENNReal.tsum_le_tsum fun w => atom_expectation_le A σ P n r ℓ q w
      _ = ∑ ℓ ∈ Finset.range (n + 1), ∑ q ∈ layerSet A ℓ,
          ∑ r ∈ Finset.range P.α, ENNReal.ofReal (1 / (1 - ε / 2)) := by
          refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun q hq =>
            Finset.sum_congr rfl fun r _ => ?_
          have hL : (1 : ℝ) ≤ langCount A ℓ q := by exact_mod_cast one_le_langCount A ℓ q hq
          have : 0 < 1 - ε / 2 := by linarith
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_mul]
          rw [← sum_card_layerSet]
          push_cast
          ring
  have hθb := params_theta_bound A n ε δ hn hε0 hε1
  have hθ' : ((P.α * A.unrolledCard n : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - ε / 2)) ≤
      1 / 16 * (P.θ : ℝ≥0∞) := by
    have : 0 < 1 - ε / 2 := by linarith
    calc ((P.α * A.unrolledCard n : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - ε / 2))
        = ENNReal.ofReal ((P.α : ℝ) * A.unrolledCard n * (1 / (1 - ε / 2))) := by
          rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast]
          push_cast
          rfl
      _ ≤ ENNReal.ofReal ((P.θ : ℝ) / 16) := ENNReal.ofReal_le_ofReal hθb.1
      _ = 1 / 16 * (P.θ : ℝ≥0∞) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_natCast,
            ENNReal.div_eq_inv_mul, one_div]
          norm_num
  have hmk : D.toOuterMeasure (Over ∩ Badᶜ) * P.θ ≤ ∑' st, D st * F st := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun st => ?_
    by_cases h : st ∈ Over ∩ Badᶜ
    · rw [Set.indicator_of_mem h]
      gcongr
      exact (Nat.cast_le.2 h.1).trans (hpt st h.2)
    · rw [Set.indicator_of_notMem h, zero_mul]
      exact zero_le
  exact (ENNReal.mul_le_mul_iff_left (by exact_mod_cast hθb.2.ne') (by simp)).mp
    (hmk.trans (hEF.trans hθ'))


/-- **Lemma proba_S(q)** (analysis.tex:10-13): in `countNFAcore*` with the paper's
parameters, the stored samples reach `θ` with probability at most `1/8`.

PAPER: analysis.tex:10-13 (statement), analysis.tex:488-523 (proof). -/
theorem proba_S_star (hprior : Nfa.Prior) {Q : Type} [Fintype Q] [LinearOrder Q]
    (A : Nfa.PaperNFA Q) (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ)
    (hn : 1 ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (coreLawStar A σ (Nfa.params A n ε δ) n).toOuterMeasure
      {st | (Nfa.params A n ε δ).θ ≤ storedTotal A n (Nfa.params A n ε δ) st} ≤ 1 / 8 := by
  set P := Nfa.params A n ε δ
  set D := coreLawStar A σ P n
  set Over := {st : CoreState Q | P.θ ≤ storedTotal A n P st}
  set Bad := {st : CoreState Q |
    ∃ ℓ ≤ n, ∃ q ∈ layerSet A ℓ, st.p ℓ q ∉ goodWindow ε (langCount A ℓ q : ℝ)}
  -- eq. decompose_for_number_of_sample (analysis.tex:489-493)
  have hsplit : Over ⊆ (Over ∩ Badᶜ) ∪ Bad := by
    intro st hst
    by_cases hb : st ∈ Bad
    · exact Or.inr hb
    · exact Or.inl ⟨hst, hb⟩
  -- the Markov bound of analysis.tex:494-523
  have hmarkov : D.toOuterMeasure (Over ∩ Badᶜ) ≤ 1 / 16 :=
    proba_S_star_markov A σ n ε δ hn hε0 hε1
  calc D.toOuterMeasure Over ≤ D.toOuterMeasure ((Over ∩ Badᶜ) ∪ Bad) :=
        MeasureTheory.measure_mono hsplit
    _ ≤ D.toOuterMeasure (Over ∩ Badᶜ) + D.toOuterMeasure Bad :=
        MeasureTheory.measure_union_le _ _
    _ ≤ 1 / 16 + 1 / 16 := add_le_add hmarkov (proba_p_star hprior A σ n ε δ hn hε0 hε1)
    _ = 1 / 8 := by
        rw [ENNReal.div_add_div_same, show (1 : ENNReal) + 1 = 2 by norm_num]
        rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        norm_num

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · Markov half `proba_S_star_markov` here; atoms bound in `AtomExpectationLe`
* r1 · open · reduced to the Markov bound `hmarkov` via `proba_p_star`
-/
