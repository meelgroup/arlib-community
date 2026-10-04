import Mathlib.Data.Finset.Card

/-- Proof-side owner for `Esa22Copy.F0_eq_dedup_length`.  Stated over the body of
`Esa22Copy.F0 A` (`A.toFinset.card`, definitionally equal) because
`Esa22Copy.Model.Prelude` imports this file and so cannot be imported back. -/
theorem Esa22Copy.Analysis.F0_eq_dedup_length_proof {n : ℕ} (A : List (Fin n)) :
    A.toFinset.card = A.dedup.length := by
  exact List.card_toFinset A
