import Formalization3sum.Model.Program
import Formalization3sum.Interface.Pseudocode
import Formalization3sum.Interface.Encoding
import Formalization3sum.Model.Prior
import Formalization3sum.Model.Prelude
import Formalization3sum.Model.Operations

/-!
# The program and the model are the same algorithm

`Formalization3sum.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`Formalization3sum.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`Formalization3sum.Model.Program`; this file is only the transport for correctness.

`directRun_toFinset_eq_directAnswerSet` converts the program's answer list to
the set-valued pseudocode view.
-/

set_option autoImplicit false

namespace Formalization3sum

/-- The pseudocode view forgets the answer list’s order, so the program value must be converted with `List.toFinset` before the two sides can be equated. This equality unfolds through `Interface.directAnswers`; it does not establish equality with `wantedAnswerSet` or address the missing sparse algorithm. -/
theorem directRun_toFinset_eq_directAnswerSet {N D : ℕ} (a : Formalization3sum.Model.Input N D) : (Formalization3sum.Program.directRun a).val.toFinset = Formalization3sum.Interface.directAnswerSet a := by
  simp [Formalization3sum.Interface.directAnswerSet]

end Formalization3sum

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `directRun_toFinset_eq_directAnswerSet` by the direct run value equation.
-/
