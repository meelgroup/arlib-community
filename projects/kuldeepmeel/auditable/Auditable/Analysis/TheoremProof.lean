import Auditable.Interface.Pseudocode
import Auditable.Interface.ProgramModel
import Auditable.Analysis.TheoremSoundProof
import Auditable.Analysis.TheoremCompleteProof
import Auditable.Analysis.TheoremOneQueryProof
import Auditable.Analysis.TheoremQuerySizeProof

/-!
# The proof-side root

This module is created when `Interface/` is finished.  A successful
correctness reduction writes the pseudocode-side capstone here; until then the
decomposition may build its direct proof underneath `Analysis/`.

`finalAudit_proof` assembles thm:finalaudit from its four parts (soundness,
completeness, one query, query size), each proved in its own `Analysis/` module.
-/

set_option autoImplicit false

namespace Auditable.Analysis

open Auditable Auditable.Model.Operations

/-- Proof-side owner for `Auditable.finalAudit`: the conjunction of the four parts. -/
theorem finalAudit_proof (hprior : Prior) {n : ℕ} (hn : 12 ≤ n) (F : CNF n) :
    (∀ K : Cert (nPrime n), (Program.countAuditor F K).val = Verdict.verified →
        (solCount F : ℝ) / 4 ≤ estimate (copies n) K.chigh ∧
          estimate (copies n) K.chigh ≤ 16 * (solCount F : ℝ)) ∧
      (1 ≤ solCount F →
        (Program.countAuditor F (Program.afCounter F).val).val = Verdict.verified) ∧
      (∀ K : Cert (nPrime n),
        (Program.countAuditor F K).cost Op.sigma2Query = 1 ∧
          (Program.countAuditor F K).cost Op.holesQuery = 0 ∧
          (Program.countAuditor F K).cost Op.stockQuery = 0) ∧
      (∀ K : Cert (nPrime n),
        (Program.countAuditor F K).cost Op.sigma2Var = (K.chigh + 2) * nPrime n + K.clow) :=
  ⟨fun K hK => finalAudit_sound_proof hprior hn F K hK,
    fun hsat => finalAudit_complete_proof hprior hn F hsat,
    fun K => finalAudit_oneQuery_proof hprior F K,
    fun K => finalAudit_querySize_proof hprior F K⟩

end Auditable.Analysis
