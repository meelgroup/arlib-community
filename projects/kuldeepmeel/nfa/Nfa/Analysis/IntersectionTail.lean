import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The intersection tail bound

`intersection_tail_bound` is Proposition chernoff_intersections (background.tex:65-71):
if every intersection of `|S|` of the events `E_1, …, E_B` has probability at most
`c^{|S|}`, then at least half of them occur with probability at most
`binom(B, ⌈B/2⌉) c^{⌈B/2⌉} ≤ 2^B c^{⌈B/2⌉}`.  The proof is the paper's: at least
`⌈B/2⌉` events occurring puts the outcome in the intersection over some `⌈B/2⌉`-set,
and there are at most `2^B` such sets.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Nfa.Analysis

open Classical in
/-- **Proposition chernoff_intersections** (background.tex:65-71), before the final
`c^{⌈B/2⌉} ≤ c^{B/2}`: if `Pr[⋂_{b ∈ F} E_b] ≤ c^{|F|}` for every `F`, then
`Pr[#{b | E_b} ≥ B/2] ≤ 2^B c^{⌈B/2⌉}`.

PAPER: background.tex:65-71. -/
theorem intersection_tail_bound {α : Type} {B : ℕ} (ν : PMF α) (E : Fin B → Set α)
    (c : ℝ≥0∞) (h : ∀ F : Finset (Fin B), ν.toOuterMeasure {x | ∀ b ∈ F, x ∈ E b} ≤ c ^ F.card) :
    ν.toOuterMeasure {x | B ≤ 2 * (Finset.univ.filter fun b => x ∈ E b).card}
      ≤ 2 ^ B * c ^ ((B + 1) / 2) := by
  classical
  set k := (B + 1) / 2
  have hsub : {x | B ≤ 2 * (Finset.univ.filter fun b => x ∈ E b).card} ⊆
      ⋃ F ∈ (Finset.univ : Finset (Fin B)).powersetCard k, {x | ∀ b ∈ F, x ∈ E b} := by
    intro x hx
    have hk : k ≤ (Finset.univ.filter fun b => x ∈ E b).card := by
      simp only [Set.mem_ofPred_eq] at hx; omega
    obtain ⟨F, hF, hFc⟩ := Finset.exists_subset_card_eq hk
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨F, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hFc⟩, fun b hb => ?_⟩
    exact (Finset.mem_filter.1 (hF hb)).2
  calc ν.toOuterMeasure {x | B ≤ 2 * (Finset.univ.filter fun b => x ∈ E b).card}
      ≤ ν.toOuterMeasure
          (⋃ F ∈ (Finset.univ : Finset (Fin B)).powersetCard k, {x | ∀ b ∈ F, x ∈ E b}) :=
        MeasureTheory.measure_mono hsub
    _ ≤ ∑ F ∈ (Finset.univ : Finset (Fin B)).powersetCard k,
          ν.toOuterMeasure {x | ∀ b ∈ F, x ∈ E b} :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ F ∈ (Finset.univ : Finset (Fin B)).powersetCard k, c ^ k := by
        refine Finset.sum_le_sum fun F hF => ?_
        rw [← (Finset.mem_powersetCard.1 hF).2]
        exact h F
    _ = (B.choose k : ℝ≥0∞) * c ^ k := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ 2 ^ B * c ^ k := by
        gcongr
        exact_mod_cast (Nat.choose_le_two_pow B k)

end Nfa.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · union over the `⌈B/2⌉`-subsets, `binom(B, k) ≤ 2^B`
-/
