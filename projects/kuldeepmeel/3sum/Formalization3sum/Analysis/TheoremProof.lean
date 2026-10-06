import Formalization3sum.Analysis.CorrectProof
import Formalization3sum.Analysis.FixedTimeProof
import Formalization3sum.Analysis.GeneralTimeProof
import Formalization3sum.Analysis.WordMagnitudeProof

set_option autoImplicit false

namespace Formalization3sum

open Model

/-- Assemble the four frontier proofs for the capstone. -/
theorem Analysis.formalization3sum_main_proof (hprior : Prior) :
    (∀ (N D : ℕ) (a : Input N D) (p : Fin N × Fin N),
      p ∈ a.W → (p, wantedValue a p) ∈ (Program.directRun a).val) ∧
    (∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ (N D : ℕ) (a : Input N D),
        0 < N → 0 < D → n₀ ≤ N → D ^ 18 ≤ N →
        magnitudeBound B a →
        (a.W.card : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt D →
        ((Arlib.Computation.Charged.steps Operations.rate
          (Program.directRun a) : ℕ) : ℝ) ≤
          C * (N : ℝ) ^ 2 / (D : ℝ) ^ ((63 : ℝ) / 1000)) ∧
    (∀ (ε κ : ℝ), ε < (301 : ℝ) / 2500 → 0 < κ →
      ∃ γ : ℝ, 0 < γ ∧
      ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
        ∀ (N D : ℕ) (a : Input N D),
          0 < N → 0 < D → n₀ ≤ N →
          magnitudeBound B a →
          (D : ℝ) ≤ (N : ℝ) ^ ε →
          (a.W.card : ℝ) ≤ (N : ℝ) ^ 2 / (D : ℝ) ^ κ →
          ((Arlib.Computation.Charged.steps Operations.rate
            (Program.directRun a) : ℕ) : ℝ) ≤
            C * (N : ℝ) ^ 2 / (D : ℝ) ^ γ) ∧
    (∀ B : ℕ, ∃ C : ℕ, ∀ (N D : ℕ) (a : Input N D),
      0 < N → 0 < D → D ≤ N → magnitudeBound B a →
      ∀ (p : Fin N × Fin N) (s : Finset (Fin D)),
        Int.natAbs (∑ k ∈ s, a.X p.1 k * a.Y k p.2) ≤
          2 ^ (C * (Nat.log2 (N + 1) + 1))) := by
  exact ⟨Formalization3sum.Analysis.formalization3sum_correct_proof hprior,
    Formalization3sum.Analysis.formalization3sum_fixed_time_proof hprior,
    Formalization3sum.Analysis.formalization3sum_general_time_proof hprior,
    Formalization3sum.Analysis.formalization3sum_word_magnitude_proof hprior⟩

end Formalization3sum
