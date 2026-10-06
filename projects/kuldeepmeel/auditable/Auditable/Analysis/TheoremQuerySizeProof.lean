import Auditable.Model.Prior
import Auditable.Model.Run
import Auditable.Meta.ModelClosure
import Auditable.Interface.Encoding
import Auditable.Interface.Pseudocode
import Auditable.Interface.ProgramModel

open Auditable.Model.Operations

/-- Proof-side owner for `Auditable.finalAudit_querySize`; its statement is fixed by the proof charter. -/
theorem Auditable.Analysis.finalAudit_querySize_proof (hprior : Prior) {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) : (Program.countAuditor F K).cost Op.sigma2Var = (K.chigh + 2) * nPrime n + K.clow := by
  rw [Auditable.Interface.countAuditor_eq]
  simp [Auditable.Model.Operations.sigma2Oracle, Auditable.Model.Operations.natLe,
    apply_ite (fun p : Arlib.Computation.Charged Op Cell Verdict => p.cost),
    Pi2Query.size, Program.auditQuery]
  ring

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · unfold via `countAuditor_eq`, `simp` the oracle costs and `auditQuery`'s size, `ring`
-/
