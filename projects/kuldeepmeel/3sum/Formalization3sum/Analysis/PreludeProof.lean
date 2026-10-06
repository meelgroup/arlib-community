import Formalization3sum.Model.Vocabulary

/-- INTERNAL: Expands the requested matrix-product entry into its defining finite sum. -/
theorem Formalization3sum.Analysis.wantedValue_eq_sum_proof {N D : ℕ} (a : Formalization3sum.Model.Input N D) (p : Fin N × Fin N) : Formalization3sum.Model.wantedValue a p = ∑ k : Fin D, a.X p.1 k * a.Y k p.2 := by
  rfl

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · the matrix-product entry unfolds definitionally to the finite sum.
-/
