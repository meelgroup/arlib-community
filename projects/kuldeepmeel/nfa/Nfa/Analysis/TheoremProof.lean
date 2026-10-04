import Nfa.Interface.Pseudocode
import Nfa.Interface.ProgramModel
import Nfa.Analysis.TheoremAccuracyProof
import Nfa.Analysis.TheoremTimeProof

/-!
# The proof-side root

This module is created when `Interface/` is finished.  A successful
correctness reduction writes the pseudocode-side capstone here; until then the
decomposition may build its direct proof underneath `Analysis/`.

`countNFA_main_result_of_halves` assembles theorem:main_result from its accuracy
half and its running-time half, taken as hypotheses so that the surface
`Nfa.countNFA_main_result` closes by citing `Nfa.countNFA_correct` and
`Nfa.countNFA_time`.
-/

namespace Nfa.Analysis

/-- Assembly of theorem:main_result from its accuracy and running-time halves. -/
theorem countNFA_main_result_of_halves
    (hcorrect : ∀ {Q : Type} [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q)
      (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ),
      1 ≤ n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      1 - δ ≤ ((Nfa.Run.output A σ n ε δ).toOuterMeasure
        (Arlib.relErr ε (Nfa.sliceCount A n : ℝ))).toReal)
    (htime : ∃ C : ℝ, ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q)
      (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ) (MM : ℕ → ℕ),
      1 ≤ n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      (∀ m, m ^ 2 ≤ MM m) → (∀ m, MM m ≤ m ^ 3) →
      ∀ c ∈ (Nfa.Run.run A σ n ε δ).support,
        (Arlib.Computation.Charged.steps
            (Nfa.Model.Operations.rate MM (Fintype.card Q)) c : ℝ) ≤
          C * (n : ℝ) ^ 2 * (MM (Fintype.card Q) : ℝ) *
            Real.log (16 * ((n : ℝ) + 1) * (Fintype.card Q : ℝ)) *
            (ε ^ 2)⁻¹ * (1 - ε)⁻¹ * (⌈8 * Real.log (1 / δ)⌉₊ : ℝ)) :
    ∃ C : ℝ, ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : Nfa.PaperNFA Q)
      (σ : Nfa.Selector A) (n : ℕ) (ε δ : ℝ) (MM : ℕ → ℕ),
      1 ≤ n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      (∀ m, m ^ 2 ≤ MM m) → (∀ m, MM m ≤ m ^ 3) →
      1 - δ ≤ ((Nfa.Run.output A σ n ε δ).toOuterMeasure
          (Arlib.relErr ε (Nfa.sliceCount A n : ℝ))).toReal ∧
      ∀ c ∈ (Nfa.Run.run A σ n ε δ).support,
        (Arlib.Computation.Charged.steps
            (Nfa.Model.Operations.rate MM (Fintype.card Q)) c : ℝ) ≤
          C * (n : ℝ) ^ 2 * (MM (Fintype.card Q) : ℝ) *
            Real.log (16 * ((n : ℝ) + 1) * (Fintype.card Q : ℝ)) *
            (ε ^ 2)⁻¹ * (1 - ε)⁻¹ * (⌈8 * Real.log (1 / δ)⌉₊ : ℝ) := by
  obtain ⟨C, hC⟩ := htime
  exact ⟨C, fun Q _ _ A σ n ε δ MM hn hε0 hε1 hδ0 hδ1 hlo hhi =>
    ⟨hcorrect A σ n ε δ hn hε0 hε1 hδ0 hδ1,
      hC Q A σ n ε δ MM hn hε0 hε1 hδ0 hδ1 hlo hhi⟩⟩

end Nfa.Analysis
