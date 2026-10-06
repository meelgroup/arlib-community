import Formalization3sum.Meta.ModelClosure
import Formalization3sum.Model.Prior
import Formalization3sum.Model.Program
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Formalization3sum.Interface.Encoding
import Formalization3sum.Interface.Pseudocode
import Formalization3sum.Interface.ProgramModel

/-!
# Fixed-time bound for the current charged program

The proof below establishes the stated inequality because every body in
`Program.directRun` and `Program.directEntry` has zero charged steps. It therefore
does not establish the paper's operation bound for its sparse algorithm. The
direct fallback is the only program currently implemented, and its matrix reads,
integer arithmetic, sorting, and answer writes are uncharged.

MODEL: Formalization3sum.Program.directRun — implement the paper's charged sparse branch for large dimensions and charge the direct fallback's primitive operations.
PRESERVES: ∀ {N D : ℕ} (a : Formalization3sum.Model.Input N D) (p : Fin N × Fin N), p ∈ a.W → (p, Formalization3sum.Model.wantedValue a p) ∈ (Formalization3sum.Program.directRun a).val
-/

/-- PAPER: 01-intro.tex:85-90; 04-general.tex:342-364.
The stated time bound is measured by the current `directRun` tally. -/
theorem Formalization3sum.Analysis.formalization3sum_fixed_time_proof (hprior : Formalization3sum.Prior) : ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (N D : ℕ) (a : Formalization3sum.Model.Input N D), 0 < N → 0 < D → n₀ ≤ N → D ^ 18 ≤ N → Formalization3sum.Model.magnitudeBound B a → (a.W.card : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt D → ((Arlib.Computation.Charged.steps Formalization3sum.Model.Operations.rate (Formalization3sum.Program.directRun a) : ℕ) : ℝ) ≤ C * (N : ℝ) ^ 2 / (D : ℝ) ^ ((63 : ℝ) / 1000) := by
  intro B
  refine ⟨1, by norm_num, 0, ?_⟩
  intro N D a hN hD _ _ _ _
  have hEntry (p : Fin N × Fin N) :
      Arlib.Computation.Charged.steps Formalization3sum.Model.Operations.rate
        (Formalization3sum.Program.directEntry a p) = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [Formalization3sum.Program.directEntry] using
      (Arlib.Computation.Charged.steps_foldl_le
        (C := Formalization3sum.Model.Operations.rate) (k := 0)
        (f := fun (acc : ℤ) (k : Fin D) =>
          (pure (acc + a.X p.1 k * a.Y k p.2) :
            Arlib.Computation.Charged Formalization3sum.Model.Operations.Op
              Formalization3sum.Model.Operations.Cell ℤ))
        (by intro acc k; simp)
        (List.finRange D) 0)
  have hRun : Arlib.Computation.Charged.steps Formalization3sum.Model.Operations.rate
      (Formalization3sum.Program.directRun a) = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [Formalization3sum.Program.directRun, hEntry] using
      (Arlib.Computation.Charged.steps_foldl_le
        (C := Formalization3sum.Model.Operations.rate) (k := 0)
        (f := fun (answers : List ((Fin N × Fin N) × ℤ)) position => do
          let v ← Formalization3sum.Program.directEntry a position
          pure ((position, v) :: answers))
        (by intro answers position; simp [hEntry])
        (a.W.sort (Prod.Lex (· < ·) (· ≤ ·))) [])
  rw [hRun]
  norm_num only [Nat.cast_zero, one_mul]
  apply div_nonneg
  · positivity
  · positivity

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · both nested folds cost zero because their bodies contain only `pure` and a zero-cost bind; this exposes the current model gap.
-/
