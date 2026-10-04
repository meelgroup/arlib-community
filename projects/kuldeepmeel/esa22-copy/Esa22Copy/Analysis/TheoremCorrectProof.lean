import Esa22Copy.Model.Prior
import Esa22Copy.Model.Prelude
import Esa22Copy.Model.Run
import Esa22Copy.Meta.ModelClosure
import Arlib.Prelude
import Esa22Copy.Interface.Encoding
import Esa22Copy.Interface.Pseudocode
import Esa22Copy.Interface.ProgramModel
import Esa22Copy.Analysis.FailProbLe
import Esa22Copy.Analysis.ErrfailProbLe

set_option autoImplicit false

namespace Esa22Copy.Analysis

open Esa22Copy.Model Arlib.Computation
open Esa22Copy.Interface.Pseudocode MeasureTheory

/-- Proof-side owner for `Esa22Copy.f0Estimator_correct`; its statement is fixed by the proof charter.

The paper's assembly (esa22-final.tex:506-521): transport `output` to the
pseudocode law `outputLaw` (`output_eq_outputLaw`), then
`Pr[Error] ≤ Pr[Fail] + Pr[Error ∩ ¬Fail] ≤ δ/8 + δ/2 ≤ δ` by Claim lm:fail
(`fail_prob_le`) and Claim claim:errfail (`errfail_prob_le`).
PAPER: esa22-final.tex:501-521 -/
-- in namespace Esa22Copy.Analysis; open Esa22Copy Esa22Copy.Model Arlib.Computation
theorem f0Estimator_correct_proof (hprior : Prior) {n : ℕ} (A : List (Fin n)) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) : ENNReal.ofReal (1 - δ) ≤ (output A ε δ).toOuterMeasure {o | ∃ c : ℕ, o = some c ∧ (c : ℝ) ∈ Arlib.relErr ε (F0 A : ℝ)} := by
  rw [(output_eq_outputLaw A ε δ).2]
  set P := outputLaw A ε δ
  set G : Set (Option ℕ) := {o | ∃ c : ℕ, o = some c ∧ (c : ℝ) ∈ Arlib.relErr ε (F0 A : ℝ)}
  set B : Set (Option ℕ) := {o | ∃ c : ℕ, o = some c ∧ (c : ℝ) ∉ Arlib.relErr ε (F0 A : ℝ)}
  -- every answer is good, ⊥ (`Fail`), or a non-⊥ bad value (`Error ∩ ¬Fail`)
  have hcover : (Set.univ : Set (Option ℕ)) ⊆ G ∪ ({none} ∪ B) := by
    rintro (_ | c) _
    · exact Or.inr (Or.inl rfl)
    · by_cases h : (c : ℝ) ∈ Arlib.relErr ε (F0 A : ℝ)
      · exact Or.inl ⟨c, rfl, h⟩
      · exact Or.inr (Or.inr ⟨c, rfl, h⟩)
  have h1 : (1 : ENNReal) ≤
      P.toOuterMeasure G + (ENNReal.ofReal (δ / 8) + ENNReal.ofReal (δ / 2)) := by
    calc (1 : ENNReal) = P.toOuterMeasure Set.univ :=
            ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)).symm
      _ ≤ P.toOuterMeasure (G ∪ ({none} ∪ B)) := measure_mono hcover
      _ ≤ P.toOuterMeasure G + (P.toOuterMeasure {none} + P.toOuterMeasure B) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ _ := add_le_add le_rfl (add_le_add (fail_prob_le A ε δ hε0 hε1 hδ0 hδ1)
            (errfail_prob_le A ε δ hε0 hε1 hδ0 hδ1))
  have hsum : ENNReal.ofReal (δ / 8) + ENNReal.ofReal (δ / 2) =
      ENNReal.ofReal (δ / 8 + δ / 2) :=
    (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  rw [hsum] at h1
  have h2 : ENNReal.ofReal (1 - δ) + ENNReal.ofReal (δ / 8 + δ / 2) ≤ 1 := by
    rw [← ENNReal.ofReal_add (by linarith) (by positivity)]
    exact ENNReal.ofReal_le_one.2 (by linarith)
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 (h2.trans h1)

end Esa22Copy.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · from `fail_prob_le` and `errfail_prob_le` (both closed, no `sorry`); the only open dependency is `Esa22Copy.output_eq_outputLaw` (Interface/ProgramModel.lean, another owner)
-/
