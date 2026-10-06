import Formalization3sum.Meta.ModelClosure
import Formalization3sum.Model.Prior
import Formalization3sum.Model.Program
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Formalization3sum.Analysis.CorrectProof
import Formalization3sum.Analysis.FixedTimeProof
import Formalization3sum.Analysis.GeneralTimeProof
import Formalization3sum.Analysis.WordMagnitudeProof
import Formalization3sum.Analysis.TheoremProof

/-!
# Sparse thin matrix product: headline audit surface

Correspondence ledger:
* 01-intro.tex:88–90, exact requested entries -> `formalization3sum_correct`;
  `(XY)[i,j]` is `Model.wantedValue`, cross-checked with the finite sum by
  `Model.wantedValue_eq_sum` (`Matrix.mul_apply`).
* 01-intro.tex:88–90, fixed `0.063` and general `ε < 0.1204` bounds ->
  `formalization3sum_fixed_time` and `formalization3sum_general_time`.
  `B` is uniform across each family, while the constants and threshold may
  depend on `B` (and on `ε, κ` in the general clause). These are statement
  decisions resolving the paper's asymptotic notation. The fixed guard is
  `D^18 ≤ N`, not the reversed inequality in the initial precondition audit.
* 01-intro.tex:88–90, `O(log N)` integer magnitude ->
  `formalization3sum_word_magnitude`. The bound includes partial inner sums,
  which are the arithmetic intermediates of the direct fallback. This is a
  proxy for the paper's reached-word claim, not an instruction-level width
  invariant; the latter is a model gap because `Program` has no word state.
  Its `D ≤ N` guard follows from either headline dimension regime, but is
  stated explicitly here to make this standalone magnitude lemma true.
* 04-general.tex:263–335, 342–397 -> no sparse construction is present in
  `Program`: `directRun` implements only the direct exceptional branch.
  Its transparent arithmetic and data access are uncharged. Consequently
  `Charged.steps Operations.rate (Program.directRun a)` does not yet measure
  the paper's operations, and the two time parts below cannot certify the
  advertised algorithm. This is a model gap and a proof obligation for later
  passes, not a claim that the direct algorithm has subquadratic real cost.
* The paper's padding, tile fit, distinct `Q` assignment, box recurrence,
  leaf partition, and small-dimension parameter selection are internal
  algorithm obligations. None is a caller hypothesis here.
-/

set_option autoImplicit false

namespace Formalization3sum

open Model

/-- Every requested entry appears with its exact integer value. -/
theorem formalization3sum_correct (hprior : Prior) :
    ∀ (N D : ℕ) (a : Input N D) (p : Fin N × Fin N),
      p ∈ a.W → (p, wantedValue a p) ∈ (Program.directRun a).val := by
    exact Formalization3sum.Analysis.formalization3sum_correct_proof hprior

/-- Fixed-range operation bound, using the operation rate of `Operations`.
The currently referenced direct program lacks charged primitive arithmetic. -/
theorem formalization3sum_fixed_time (hprior : Prior) :
    ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ (N D : ℕ) (a : Input N D),
        0 < N → 0 < D → n₀ ≤ N → D ^ 18 ≤ N →
        magnitudeBound B a →
        (a.W.card : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt D →
        ((Arlib.Computation.Charged.steps Operations.rate
          (Program.directRun a) : ℕ) : ℝ) ≤
          C * (N : ℝ) ^ 2 / (D : ℝ) ^ ((63 : ℝ) / 1000) := by
    exact Formalization3sum.Analysis.formalization3sum_fixed_time_proof hprior

/-- General-range operation bound; `γ` follows `ε` and `κ`. -/
theorem formalization3sum_general_time (hprior : Prior) :
    ∀ (ε κ : ℝ), ε < (301 : ℝ) / 2500 → 0 < κ →
      ∃ γ : ℝ, 0 < γ ∧
      ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
        ∀ (N D : ℕ) (a : Input N D),
          0 < N → 0 < D → n₀ ≤ N →
          magnitudeBound B a →
          (D : ℝ) ≤ (N : ℝ) ^ ε →
          (a.W.card : ℝ) ≤ (N : ℝ) ^ 2 / (D : ℝ) ^ κ →
          ((Arlib.Computation.Charged.steps Operations.rate
            (Program.directRun a) : ℕ) : ℝ) ≤
            C * (N : ℝ) ^ 2 / (D : ℝ) ^ γ := by
    exact Formalization3sum.Analysis.formalization3sum_general_time_proof hprior

/-- Magnitude of every partial inner sum computed by the direct fallback.
This does not yet assert a bound on every reached RAM word. -/
theorem formalization3sum_word_magnitude (hprior : Prior) :
    ∀ B : ℕ, ∃ C : ℕ, ∀ (N D : ℕ) (a : Input N D),
      0 < N → 0 < D → D ≤ N → magnitudeBound B a →
      ∀ (p : Fin N × Fin N) (s : Finset (Fin D)),
        Int.natAbs (∑ k ∈ s, a.X p.1 k * a.Y k p.2) ≤
          2 ^ (C * (Nat.log2 (N + 1) + 1)) := by
    exact Formalization3sum.Analysis.formalization3sum_word_magnitude_proof hprior

/-- The two headline ranges, exact output, and available word-magnitude proxy. -/
theorem formalization3sum_main (hprior : Prior) :
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
  exact Formalization3sum.Analysis.formalization3sum_main_proof hprior

end Formalization3sum

#modelClosureOfType Formalization3sum.formalization3sum_main
#print axioms Formalization3sum.formalization3sum_main

#surplusIn Formalization3sum.Model from Formalization3sum.formalization3sum_main
