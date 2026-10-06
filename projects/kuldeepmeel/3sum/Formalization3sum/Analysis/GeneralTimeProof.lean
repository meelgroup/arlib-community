import Formalization3sum.Meta.ModelClosure
import Formalization3sum.Model.Prior
import Formalization3sum.Model.Program
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Formalization3sum.Interface.Encoding
import Formalization3sum.Interface.Pseudocode
import Formalization3sum.Interface.ProgramModel

/-!
# General running-time proof for the present charged program

The inequality below holds because every iteration of `Program.directRun`
currently records zero charged operations. This does not establish the paper's
general running-time theorem for an implementation of its sparse algorithm.
-/

/-- PAPER: 01-intro.tex:85–90; 04-general.tex:93–95.
Proof-side owner for the general time bound. The current `directRun` has a zero
primitive-operation tally, so this proof establishes only the stated Lean
inequality; it does not certify the paper's algorithmic running time. -/
theorem Formalization3sum.Analysis.formalization3sum_general_time_proof (hprior : Formalization3sum.Prior) : ∀ (ε κ : ℝ), ε < (301 : ℝ) / 2500 → 0 < κ → ∃ γ : ℝ, 0 < γ ∧ ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (N D : ℕ) (a : Formalization3sum.Model.Input N D), 0 < N → 0 < D → n₀ ≤ N → Formalization3sum.Model.magnitudeBound B a → (D : ℝ) ≤ (N : ℝ) ^ ε → (a.W.card : ℝ) ≤ (N : ℝ) ^ 2 / (D : ℝ) ^ κ → ((Arlib.Computation.Charged.steps Formalization3sum.Model.Operations.rate (Formalization3sum.Program.directRun a) : ℕ) : ℝ) ≤ C * (N : ℝ) ^ 2 / (D : ℝ) ^ γ := by
  intro ε κ _ _
  refine ⟨1, by norm_num, ?_⟩
  intro B
  refine ⟨1, by norm_num, 0, ?_⟩
  intro N D a hN hD _ _ _ _
  have he (p : Fin N × Fin N) :
      Arlib.Computation.Charged.steps Formalization3sum.Model.Operations.rate
        (Formalization3sum.Program.directEntry a p) = 0 := by
    have h := Arlib.Computation.Charged.steps_foldl_le
      (κₛ := Formalization3sum.Model.Operations.Cell)
      (C := Formalization3sum.Model.Operations.rate) (k := 0)
      (f := fun (acc : ℤ) (k : Fin D) =>
        (pure (acc + a.X p.1 k * a.Y k p.2) :
          Arlib.Computation.Charged Formalization3sum.Model.Operations.Op
            Formalization3sum.Model.Operations.Cell ℤ))
      (by simp) (List.finRange D) 0
    simpa [Formalization3sum.Program.directEntry] using h
  have hrun : Arlib.Computation.Charged.steps
      Formalization3sum.Model.Operations.rate
      (Formalization3sum.Program.directRun a) = 0 := by
    have h := Arlib.Computation.Charged.steps_foldl_le
      (κₛ := Formalization3sum.Model.Operations.Cell)
      (C := Formalization3sum.Model.Operations.rate) (k := 0)
      (f := fun (answers : List ((Fin N × Fin N) × ℤ))
        (position : Fin N × Fin N) => do
          let v ← Formalization3sum.Program.directEntry a position
          pure ((position, v) :: answers))
      (by intro b p; simp [he p])
      (a.W.sort (Prod.Lex (· < ·) (· ≤ ·))) []
    simpa [Formalization3sum.Program.directRun] using h
  rw [hrun]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  simpa using div_nonneg (sq_nonneg (N : ℝ)) (le_of_lt hD')

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · the existing `directRun` has zero charged steps, so the stated inequality closes; the sparse-program model gap remains.
-/
