import Formalization3sum.Model.Program

/-!
# Specification view of the direct answer list

04-general.tex:263–335 describes normalization, outer tiling, distinct inner-set
assignments, shared encodings, a box trie, and low-order and box contributions
to each query. `Model/Program.lean` currently implements only the direct branch
for `D = 1` or bounded small dimensions (04-general.tex:69,361). Accordingly,
`directAnswers` below is the answer object for that branch alone. The box-trie
answer object cannot yet be translated from an executable model. The current
program also uses its own `Operations.Op` and `Operations.Cell` directly, so
there is no arlib operation-class indirection to collapse here.

All reads of `Charged.val` in this module are specification-only views.
-/

set_option autoImplicit false

namespace Formalization3sum.Interface

open Formalization3sum.Model
open Arlib.Computation

/-- The direct branch's per-position result, viewed outside executable code. -/
noncomputable def directEntryValue {N D : ℕ} (a : Input N D)
    (p : Fin N × Fin N) : ℤ :=
  (Program.directEntry a p).val

@[simp] theorem directEntry_val {N D : ℕ} (a : Input N D)
    (p : Fin N × Fin N) :
    (Program.directEntry a p).val = directEntryValue a p := by
  rfl

/-- The answer list produced by the direct branch, in its output-write order. -/
noncomputable def directAnswers {N D : ℕ} (a : Input N D) :
    List ((Fin N × Fin N) × ℤ) :=
  (Program.directRun a).val

/-- Reading the direct run yields its answer object. -/
@[simp] theorem directRun_val {N D : ℕ} (a : Input N D) :
    (Program.directRun a).val = directAnswers a := by
  rfl

end Formalization3sum.Interface
