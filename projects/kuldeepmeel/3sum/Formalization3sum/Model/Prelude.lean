import Formalization3sum.Model.Vocabulary
import Formalization3sum.Analysis.PreludeProof

set_option autoImplicit false

namespace Formalization3sum.Model

/-- Cross-check the wanted entry against Mathlib's `Matrix.mul_apply` finite sum. -/
theorem wantedValue_eq_sum {N D : ℕ} (a : Input N D)
    (p : Fin N × Fin N) : wantedValue a p =
      ∑ k : Fin D, a.X p.1 k * a.Y k p.2 := by
    exact Formalization3sum.Analysis.wantedValue_eq_sum_proof (N := N) (D := D) a p

end Formalization3sum.Model
