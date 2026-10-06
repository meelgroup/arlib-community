import Formalization3sum.Meta.ModelClosure
import Formalization3sum.Model.Prior
import Formalization3sum.Model.Program
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Formalization3sum.Interface.Encoding
import Formalization3sum.Interface.Pseudocode
import Formalization3sum.Interface.ProgramModel

/-- INTERNAL: The direct entry fold accumulates the products of its visited coordinates. -/
theorem Formalization3sum.Analysis.directEntry_fold_value {N D : ℕ}
    (a : Formalization3sum.Model.Input N D) (p : Fin N × Fin N)
    (l : List (Fin D)) (acc : ℤ) :
    (Arlib.Computation.Charged.foldl
      (fun acc k => (pure (acc + a.X p.1 k * a.Y k p.2) :
        Arlib.Computation.Charged Formalization3sum.Model.Operations.Op
          Formalization3sum.Model.Operations.Cell ℤ)) l acc).val =
      acc + (l.map (fun k => a.X p.1 k * a.Y k p.2)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons k ks ih =>
      simp only [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_pure, List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- INTERNAL: The direct entry fold returns the matrix-product entry. -/
theorem Formalization3sum.Analysis.directEntry_value_eq_wanted {N D : ℕ}
    (a : Formalization3sum.Model.Input N D) (p : Fin N × Fin N) :
    (Formalization3sum.Program.directEntry a p).val =
      Formalization3sum.Model.wantedValue a p := by
  rw [Formalization3sum.Program.directEntry, Formalization3sum.Analysis.directEntry_fold_value]
  simp only [zero_add]
  rw [← List.sum_toFinset (fun k : Fin D => a.X p.1 k * a.Y k p.2)
    (List.nodup_finRange D), List.toFinset_finRange]
  exact (Formalization3sum.Model.wantedValue_eq_sum a p).symm

/-- INTERNAL: The direct run fold prepends one answer for each visited position. -/
theorem Formalization3sum.Analysis.directRun_fold_value {N D : ℕ}
    (a : Formalization3sum.Model.Input N D)
    (l : List (Fin N × Fin N))
    (b : List ((Fin N × Fin N) × ℤ)) :
    (Arlib.Computation.Charged.foldl (fun answers position => do
      let v ← Formalization3sum.Program.directEntry a position
      pure ((position, v) :: answers)) l b).val =
      l.reverse.map (fun p => (p, (Formalization3sum.Program.directEntry a p).val)) ++ b := by
  induction l generalizing b with
  | nil => simp
  | cons q qs ih =>
      simp only [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- INTERNAL: The modeled direct fallback returns each requested matrix-product entry.
TEXLINE: 04-general.tex:69 -/
theorem Formalization3sum.Analysis.formalization3sum_correct_proof (hprior : Formalization3sum.Prior) : ∀ (N D : ℕ) (a : Formalization3sum.Model.Input N D) (p : Fin N × Fin N), p ∈ a.W → (p, Formalization3sum.Model.wantedValue a p) ∈ (Formalization3sum.Program.directRun a).val := by
  intro N D a p hp
  rw [Formalization3sum.Program.directRun, Formalization3sum.Analysis.directRun_fold_value]
  simp only [List.append_nil, List.mem_map, List.mem_reverse]
  exact ⟨p, (Finset.mem_sort (Prod.Lex (· < ·) (· ≤ ·))).mpr hp,
    congrArg (fun v => (p, v)) (Formalization3sum.Analysis.directEntry_value_eq_wanted a p)⟩

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · direct fold values and output membership establish the correctness owner.
-/
