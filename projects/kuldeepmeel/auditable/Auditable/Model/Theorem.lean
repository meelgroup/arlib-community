import Auditable.Model.Prior
import Auditable.Model.Run
import Auditable.Meta.ModelClosure
import Auditable.Analysis.TheoremSoundProof
import Auditable.Analysis.TheoremCompleteProof
import Auditable.Analysis.TheoremOneQueryProof
import Auditable.Analysis.TheoremQuerySizeProof
import Auditable.Analysis.TheoremAfCounterDacProof
import Auditable.Analysis.TheoremAfCounterQueriesProof
import Auditable.Analysis.TheoremEqualCellsDacProof
import Auditable.Analysis.TheoremEqualCellsQueriesProof
import Auditable.Analysis.TheoremStockmeyerQueriesProof
import Auditable.Analysis.TheoremStockmeyerDacProof
import Auditable.Analysis.TheoremProof

/-!
# thm:finalaudit — the audit of `AFCounter`

The paper (finalaudit.tex:77-81): *"The audit complexity of Algorithm algo:pigeons
is `O(n log n)`."* By the definition of audit complexity (problem.tex:22-34: an
auditor in class `C = Σ₂ᴾ` making `t` calls with `r` variables per call that
certifies the counter's answer) this unpacks into four claims about
`CountAuditor`, each a part theorem below:

* `finalAudit_sound` — **soundness**, for *every* certificate `K`, not only the
  one `AFCounter` produces: if `CountAuditor(F, K)` is `Verified` then
  `|sol F| / 4 ≤ 2^{c_high / k} ≤ 16 · |sol F|` (a 16-factor DAC approximation),
  `k = ⌈log₂ n⌉`. No satisfiability hypothesis: an unsatisfiable `F` makes
  `φ_holes` false, so nothing is verified.
* `finalAudit_complete` — **completeness**: for satisfiable `F`, the auditor
  verifies `AFCounter(F)`. Without it an always-reject auditor would satisfy
  soundness with a 0-variable query. The paper's proof of thm:finalaudit does not
  argue it; it rests on the gap lemma combined.tex:117-132. The hypothesis
  `1 ≤ |sol F|` is needed: on unsatisfiable `F` `AFCounter` returns `c_high = 1`.
* `finalAudit_oneQuery` — `t = 1`: the auditor makes exactly one oracle call, to
  the `Σ₂ᴾ` oracle on a forall-exists query with a quantifier-free matrix, and no
  `Σ₃ᴾ`/witness-returning call.
* `finalAudit_querySize` — `r`: that one query has exactly
  `(c_high + 2) · n' + c_low` quantified variables, `n' = n · ⌈log₂ n⌉`.

`12 ≤ n` is the paper's own restriction (finalaudit.tex:94, "`n² > 128` for
`n ≥ 12`"); soundness and completeness use it, the two resource parts do not.

## What is *not* stated here, and why (statement problem, reported)

The paper's `O(n log n)` bound on `r` is **not** stated. Under the isolation
semantics of `φ_stock` (the one its prose and cl:stockup's proof use, see
`stockWith`), the only quantifier-free forall-exists encoding of `poscheck` needs a
copy of `z₂` per stock hash, which gives the exact size above. For `F ≡ True`,
cl:stockup forces the honest `c_high ≥ n' − log₂ n'`, so the honest query has
`Θ(n'²) = Θ(n² log² n)` variables, and the paper's `O(n log n)` fails. Under the
literal pairwise formula of stock.tex:4 the paper's count `3n' + c_low ≤ 4n'` is
right but soundness fails (`n = 12`, `F ≡ True`, `c_low = c_high = 7` with seven
block projections is verified while `2^{7/4} < 4096 / 4`). So no reading of
`φ_stock` makes the paper's four clauses true together. The refutation of the
`O(n log n)` clause for this auditor is a separate result for `Analysis/`, not part
of this headline; `finalAudit_querySize` is the honest measurement in its place.

Modelling decisions behind every name used here are recorded in the docstrings of
`Model/Prelude.lean` (vocabulary), `Model/Operations.lean` (cost currency) and
`Model/Program.lean` (the two algorithms, with five disclosed deviations from the
listings).
-/

set_option autoImplicit false

namespace Auditable

open Auditable.Model.Operations

/-- **Soundness** (finalaudit.tex:84-105): whatever certificate `K` is presented, if
the auditor verifies it then `2^{c_high / ⌈log₂ n⌉}` is within the factors `4`
below and `16` above `|sol F|`. -/
theorem finalAudit_sound (hprior : Prior) {n : ℕ} (hn : 12 ≤ n) (F : CNF n)
    (K : Cert (nPrime n)) (hK : (Program.countAuditor F K).val = Verdict.verified) :
    (solCount F : ℝ) / 4 ≤ estimate (copies n) K.chigh ∧
      estimate (copies n) K.chigh ≤ 16 * (solCount F : ℝ) := by
    exact Auditable.Analysis.finalAudit_sound_proof hprior (n := n) hn F K hK

/-- **Completeness** (problem.tex:28-31; combined.tex:117-132): on a satisfiable
`F`, the auditor verifies the certificate `AFCounter(F)` returns. -/
theorem finalAudit_complete (hprior : Prior) {n : ℕ} (hn : 12 ≤ n) (F : CNF n)
    (hsat : 1 ≤ solCount F) :
    (Program.countAuditor F (Program.afCounter F).val).val = Verdict.verified := by
    exact Auditable.Analysis.finalAudit_complete_proof hprior (n := n) hn F hsat

/-- **One oracle call** (`t = 1`, finalaudit.tex:107, 136): on any certificate the
auditor makes exactly one `Σ₂ᴾ` query and no other oracle call. -/
theorem finalAudit_oneQuery (hprior : Prior) {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) :
    (Program.countAuditor F K).cost Op.sigma2Query = 1 ∧
      (Program.countAuditor F K).cost Op.holesQuery = 0 ∧
      (Program.countAuditor F K).cost Op.stockQuery = 0 := by
    exact Auditable.Analysis.finalAudit_oneQuery_proof hprior (n := n) F K

/-- **Size of that query** (`r`, finalaudit.tex:107, 138): the `Σ₂ᴾ` query the
auditor sends on certificate `K` quantifies exactly `(c_high + 2) · n' + c_low`
Boolean variables. This replaces the paper's `O(n log n)`; see the module
docstring. -/
theorem finalAudit_querySize (hprior : Prior) {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) :
    (Program.countAuditor F K).cost Op.sigma2Var = (K.chigh + 2) * nPrime n + K.clow := by
    exact Auditable.Analysis.finalAudit_querySize_proof hprior (n := n) F K

/-- **thm:finalaudit**, as formalized: the auditor `CountAuditor` is sound for every
certificate, complete for `AFCounter` on satisfiable formulas, makes one `Σ₂ᴾ`
query, and that query has `(c_high + 2) · n' + c_low` variables. -/
theorem finalAudit (hprior : Prior) {n : ℕ} (hn : 12 ≤ n) (F : CNF n) :
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
        (Program.countAuditor F K).cost Op.sigma2Var = (K.chigh + 2) * nPrime n + K.clow) := by
    exact Auditable.Analysis.finalAudit_proof hprior (n := n) hn F

/-! ## The theorem after Algorithm algo:pigeons (combined.tex:60-67)

*"Algorithm algo:pigeons solves DAC and makes `O(n log n)` calls to `Σ₃ᴾ` oracle."*
This is a claim about the counter `AFCounter` itself, not about `CountAuditor`. It
splits into the accuracy of `CntEst = 2^{c_high / k}` on the one deterministic run
(`afCounter_dac`) and the oracle calls that run is charged (`afCounter_queries`).

* **Factor and range.** The theorem names no approximation factor; its proof
  defers to the correctness of Algorithm algo:stock, which ends in
  `|sol F| / 16 ≤ CntEst ≤ 16 · |sol F|` "for `n ≥ 4`" (stock.tex:129,133). Both the
  factor `16` and `4 ≤ n` are taken from there. (The same argument with
  `k = ⌈log₂ n⌉` gives the sharper `|sol F| / 4 ≤ CntEst < 8 · |sol F|` and needs
  only `n ≥ 2`; that is a remark, not what is stated.)
* **Satisfiability (statement problem, reported).** "Solves DAC" (prelim.tex:39-43)
  is false for unsatisfiable `F`: for `F = [[]]` (one empty clause) `φ_stock(1)`
  holds vacuously, so `c_high = 1` and `CntEst = 2^{1/k} > 0 = 16 · |sol F|`. The DAC
  part therefore carries `1 ≤ |sol F|`, which the paper does not state.
* **Which oracle.** The theorem says "`Σ₃ᴾ` oracle"; its proof (combined.tex:64)
  counts at most `n log n` calls of each of the two oracles. Both are bounded here
  separately, `≤ n' = n · ⌈log₂ n⌉` each, and the audit-style `Σ₂ᴾ` call is shown
  absent. Every one of these calls can be answered by a `Σ₃ᴾ` oracle (`Σ₂ᴾ ⊆ Σ₃ᴾ`),
  which is the sense in which the one-oracle phrasing is true.
* **Oracle model.** Each call returns its witness (the hashes) at unit cost, as
  the listing's `(assign, ret) ← …QBFCheck(…)` does (`Model/Operations.lean`). The
  call bound is in that model; with decision-only oracles, extracting the hashes by
  self-reduction costs further calls per round.
* **Algorithm algo:stock.** The proof's "`AFCounter` returns the same output as
  Algorithm algo:stock" holds only for `(c_high, CntEst)` and only with Stock's
  `break` inside the `if` (stock.tex:111); the listing at stock.tex:97 puts it
  outside, so read literally Stock stops after `m = 1`. No Stock program is stated:
  the claim is about `AFCounter`'s own `c_high`.
-/

/-- **`AFCounter` solves DAC** (combined.tex:60-64, factor and range from
stock.tex:129,133): on a satisfiable `F` over `n ≥ 4` variables, the estimate
`CntEst = 2^{c_high / ⌈log₂ n⌉}` read off `AFCounter(F)` is within a factor `16` of
`|sol F|`. `hsat` is not in the paper and cannot be dropped (`F = [[]]`, see above). -/
theorem afCounter_dac (hprior : Prior) {n : ℕ} (hn : 4 ≤ n) (F : CNF n)
    (hsat : 1 ≤ solCount F) :
    (solCount F : ℝ) / 16 ≤ estimate (copies n) (Program.afCounter F).val.chigh ∧
      estimate (copies n) (Program.afCounter F).val.chigh ≤ 16 * (solCount F : ℝ) := by
    exact Auditable.Analysis.afCounter_dac_proof hprior (n := n) hn F hsat

/-- **`O(n log n)` oracle calls** (combined.tex:61, 64): on every `F`, one run of
`AFCounter` makes at most `n' = n · ⌈log₂ n⌉` `3QBFCheck` (`Σ₃ᴾ`) calls, at most `n'`
`2QBFCheck` (`Σ₂ᴾ`) calls, and no other oracle call; each call is a unit-cost,
witness-returning oracle call. -/
theorem afCounter_queries (hprior : Prior) {n : ℕ} (F : CNF n) :
    (Program.afCounter F).cost Op.holesQuery ≤ nPrime n ∧
      (Program.afCounter F).cost Op.stockQuery ≤ nPrime n ∧
      (Program.afCounter F).cost Op.sigma2Query = 0 := by
    exact Auditable.Analysis.afCounter_queries_proof hprior (n := n) F

/-- **The theorem after Algorithm algo:pigeons**, as formalized: for `n ≥ 4` and
satisfiable `F`, `AFCounter(F)`'s estimate is a 16-factor approximation of
`|sol F|`; and for every `F` it makes at most `n · ⌈log₂ n⌉` calls to each of its two
oracles (`O(n log n)` in total, all answerable by a `Σ₃ᴾ` oracle) and no other. -/
theorem afCounterCorrect (hprior : Prior) {n : ℕ} (F : CNF n) :
    (4 ≤ n → 1 ≤ solCount F →
        (solCount F : ℝ) / 16 ≤ estimate (copies n) (Program.afCounter F).val.chigh ∧
          estimate (copies n) (Program.afCounter F).val.chigh ≤ 16 * (solCount F : ℝ)) ∧
      (Program.afCounter F).cost Op.holesQuery ≤ nPrime n ∧
      (Program.afCounter F).cost Op.stockQuery ≤ nPrime n ∧
      (Program.afCounter F).cost Op.sigma2Query = 0 :=
  ⟨fun hn hsat => afCounter_dac hprior hn F hsat, afCounter_queries hprior F⟩

/-! ## thm:intermediate — `EqualCellsCounter` (bgp.tex:101-140)

*"Algorithm algo:smallcells solves DAC and makes `O(n)` calls to a `Σ₃ᴾ` oracle."*
A claim about the counter `EqualCellsCounter` (`Program.equalCellsCounter`), split
into the accuracy of its `CntEst = ℓ · 2^m` on the one deterministic run
(`equalCells_dac`) and the oracle calls that run is charged (`equalCells_queries`).

* **Threshold (statement problem, reported).** "Solves DAC" is false as stated.
  Passing the check at `m` forces `ℓ · 2^m ≤ |sol F|` (Proposition prop:bgp), so if
  `|sol F| < 2048 n` no `m ∈ [1, n]` passes and `CntEst = 1024 n · 2^n` (with the
  `break` read literally, `2048 n`), which exceeds `16 · |sol F|` once
  `|sol F| < 128 n`. Example: `n = 4`, `F = []`, `|sol F| = 16`, `CntEst = 65536`.
  Since `|sol F| ≤ 2^n`, this happens for every `F` when `1 ≤ n ≤ 14`. The paper's
  proof picks `m₀ = ⌊log |sol F| − 12 − log n⌋`, which lies in `[1, n]` only when
  `|sol F| ≥ 8192 n`; that hypothesis is added. `4 ≤ n` is the paper's own
  (bgp.tex:178); its only remaining job is to exclude `n = 0`.
* **Sharper form.** The proof gives `ℓ · 2^m ≤ |sol F| ≤ u · 2^m` at the stopping
  round, i.e. `|sol F| / 16 ≤ CntEst ≤ |sol F|`, which is stated; it implies the
  factor-16 DAC condition `|sol F| / 16 ≤ CntEst ≤ 16 · |sol F|` of prelim.tex:39-43.
* **Hash family.** Both parts hold for every field `K` of order `2^n` and every
  encoding `bits : K ≃ (Fin n → Bool)`; the paper fixes one `GF(2^n)`. Not
  vacuous: `GaloisField 2 n` is such a field.
* **Oracle model.** `O(n)` is stated as the concrete bound `n` (bgp.tex:115). Each
  call returns its witness at unit cost (`Model/Operations.lean`); `Σ₃ᴾ` is the
  class of the query `φ_Cells` (an `∃ h ∀ α, y ∃ z` sentence), carried by the
  oracle's definition, not proved as a class membership.
* **Listing repairs.** The `break` is inside the `if` and the no-success default
  is `m = n` (Deviations 6 and 7, `Model/Program.lean`); `φ_Cells` has its prose
  meaning (`cellsWith`, `Model/Prelude.lean`).
-/

/-- **`EqualCellsCounter` solves DAC** (bgp.tex:101-113, with the threshold its proof
needs): for `n ≥ 4` and `|sol F| ≥ 8192 n`, the estimate `CntEst = 1024 n · 2^m`
returned by `EqualCellsCounter(F)` satisfies `|sol F| / 16 ≤ CntEst ≤ |sol F|`.
`hcount` is not in the paper and some such hypothesis is necessary (see above). -/
theorem equalCells_dac (hprior : Prior) {K : Type} [Field K] [FinEnum K] {n : ℕ}
    (bits : K ≃ (Fin n → Bool)) (hn : 4 ≤ n) (F : CNF n)
    (hcount : 8192 * n ≤ solCount F) :
    (solCount F : ℝ) / 16 ≤ ((Program.equalCellsCounter bits F).val.cntEst : ℝ) ∧
      ((Program.equalCellsCounter bits F).val.cntEst : ℝ) ≤ (solCount F : ℝ) := by
    exact Auditable.Analysis.equalCells_dac_proof hprior (K := K) (n := n) bits hn F hcount

/-- **`O(n)` oracle calls** (bgp.tex:103, 115): on every `F`, one run of
`EqualCellsCounter` makes at most `n` `3QBFCheck(φ_Cells)` (`Σ₃ᴾ`) calls. It is
charged in the one-primitive currency `CellsOp` (`Model/Operations.lean`), so "no
other oracle call" holds by the program's type: it cannot charge any `Op` primitive
(`holesQuery`, `stockQuery`, `sigma2Query`, …), and `CellsOp.cellsQuery` is the
only coordinate of its tally. -/
theorem equalCells_queries (hprior : Prior) {K : Type} [Field K] [FinEnum K] {n : ℕ}
    (bits : K ≃ (Fin n → Bool)) (F : CNF n) :
    (Program.equalCellsCounter bits F).cost CellsOp.cellsQuery ≤ n := by
    exact Auditable.Analysis.equalCells_queries_proof hprior (K := K) (n := n) bits F

/-- **thm:intermediate**, as formalized: for `n ≥ 4` and `|sol F| ≥ 8192 n`,
`EqualCellsCounter(F)`'s estimate satisfies `|sol F| / 16 ≤ CntEst ≤ |sol F|` (a
16-factor DAC answer); and for every `F` it makes at most `n` calls to its `Σ₃ᴾ`
oracle, the only primitive of its currency `CellsOp`. -/
theorem equalCellsCorrect (hprior : Prior) {K : Type} [Field K] [FinEnum K] {n : ℕ}
    (bits : K ≃ (Fin n → Bool)) (F : CNF n) :
    (4 ≤ n → 8192 * n ≤ solCount F →
        (solCount F : ℝ) / 16 ≤ ((Program.equalCellsCounter bits F).val.cntEst : ℝ) ∧
          ((Program.equalCellsCounter bits F).val.cntEst : ℝ) ≤ (solCount F : ℝ)) ∧
      (Program.equalCellsCounter bits F).cost CellsOp.cellsQuery ≤ n :=
  ⟨fun hn hcount => equalCells_dac hprior bits hn F hcount, equalCells_queries hprior bits F⟩

/-! ## Theorem [Stockmeyer] — `Stock` (stock.tex:114-135)

*"Algorithm algo:stock makes `O(n log n)` queries to `Σ₂ᴾ` oracle and solves DAC."*
A claim about the counter `Stock` (`Program.stockCounter`), split into the oracle
calls its one deterministic run is charged (`stockmeyer_queries`) and the accuracy
of `CntEst = 2^{v / k}`, `k = ⌈log₂ n⌉` (`stockmeyer_dac`).

* **Which coordinate is "the `Σ₂ᴾ` oracle".** Stock's calls are
  `2QBFCheck(φ_stock^{F'}(m))` (stock.tex:91), a witness-returning `Σ₂ᴾ` query,
  charged as `Op.stockQuery`. `Op.sigma2Query` is a *different* `Σ₂ᴾ`-flavoured
  primitive, the auditor's decision-only call on a syntactic `Pi2Query`; Stock never
  makes it, so that coordinate is `0`. `sigma2Query = 0` does not contradict
  "queries to a `Σ₂ᴾ` oracle": those queries are the `stockQuery` coordinate.
* **`O(n log n)`** is stated as the concrete loop length `n' = n · ⌈log₂ n⌉`
  (stock.tex:90, 133), for every `n` and `F`.
* **Factor and range.** "Solves DAC" names no factor. The proof concludes
  `|sol F| / 16 ≤ CntEst ≤ 16 · |sol F|` "for `n ≥ 4`" (stock.tex:129, 133); both are
  taken from there. (With `k = ⌈log₂ n⌉` the argument gives the sharper
  `|sol F| / 4 ≤ CntEst < 8 · |sol F|` for `n ≥ 2`; a remark, not what is stated.)
* **Satisfiability (statement problem, reported).** "Solves DAC" is false for
  unsatisfiable `F`: for `F = [[]]` (one empty clause) `F'` is unsatisfiable,
  `φ_stock^{F'}(1)` holds vacuously, so `v = 1` and `CntEst = 2^{1/k} > 0 = 16 · |sol F|`.
  The DAC part carries `1 ≤ |sol F|`, which the paper does not state; its proof uses
  it silently in the contrapositive of lm:stockexist at `v − 1 = 0`.
* **Listing repair.** The `break` is taken only on success (Deviation 8,
  `Model/Program.lean`); read literally (stock.tex:97) the theorem is false.
* **Oracle model.** Each call returns its witness at unit cost
  (`Model/Operations.lean`). `v` and `CntEst` need only the decisions; only
  `hashassgn_stock` needs the witnesses. Membership of `φ_stock` in `Σ₂ᴾ` is carried
  by the oracle's definition, not proved.
-/

/-- **`O(n log n)` queries to a `Σ₂ᴾ` oracle** (stock.tex:115, 133): on every `F`, one
run of `Stock` makes at most `n' = n · ⌈log₂ n⌉` `2QBFCheck(φ_stock)` calls (the
`Op.stockQuery` coordinate, the paper's `Σ₂ᴾ` queries), no `3QBFCheck` (`Σ₃ᴾ`) call,
and no call of the auditor's other `Σ₂ᴾ` primitive `Op.sigma2Query`. -/
theorem stockmeyer_queries (hprior : Prior) {n : ℕ} (F : CNF n) :
    (Program.stockCounter F).cost Op.stockQuery ≤ nPrime n ∧
      (Program.stockCounter F).cost Op.holesQuery = 0 ∧
      (Program.stockCounter F).cost Op.sigma2Query = 0 := by
    exact Auditable.Analysis.stockmeyer_queries_proof hprior (n := n) F

/-- **`Stock` solves DAC** (stock.tex:115, factor and range from stock.tex:129, 133):
on a satisfiable `F` over `n ≥ 4` variables, the estimate `CntEst = 2^{v / ⌈log₂ n⌉}`
read off `Stock(F)` is within a factor `16` of `|sol F|`. `hsat` is not in the paper
and cannot be dropped (`F = [[]]`, see above). -/
theorem stockmeyer_dac (hprior : Prior) {n : ℕ} (hn : 4 ≤ n) (F : CNF n)
    (hsat : 1 ≤ solCount F) :
    (solCount F : ℝ) / 16 ≤ estimate (copies n) (Program.stockCounter F).val.v ∧
      estimate (copies n) (Program.stockCounter F).val.v ≤ 16 * (solCount F : ℝ) := by
    exact Auditable.Analysis.stockmeyer_dac_proof hprior (n := n) hn F hsat

/-- **Theorem [Stockmeyer]**, as formalized: for `n ≥ 4` and satisfiable `F`,
`Stock(F)`'s estimate is a 16-factor approximation of `|sol F|`; and for every `F` it
makes at most `n · ⌈log₂ n⌉` calls to its `Σ₂ᴾ` oracle `2QBFCheck` (`Op.stockQuery`)
and no other oracle call. -/
theorem stockmeyerCorrect (hprior : Prior) {n : ℕ} (F : CNF n) :
    (4 ≤ n → 1 ≤ solCount F →
        (solCount F : ℝ) / 16 ≤ estimate (copies n) (Program.stockCounter F).val.v ∧
          estimate (copies n) (Program.stockCounter F).val.v ≤ 16 * (solCount F : ℝ)) ∧
      (Program.stockCounter F).cost Op.stockQuery ≤ nPrime n ∧
      (Program.stockCounter F).cost Op.holesQuery = 0 ∧
      (Program.stockCounter F).cost Op.sigma2Query = 0 :=
  ⟨fun hn hsat => stockmeyer_dac hprior hn F hsat, stockmeyer_queries hprior F⟩

end Auditable

#modelClosureOfType Auditable.finalAudit
#print axioms Auditable.finalAudit

#surplusIn Auditable.Model from Auditable.finalAudit Auditable.equalCellsCorrect

#modelClosureOfType Auditable.afCounterCorrect
#print axioms Auditable.afCounterCorrect

#modelClosureOfType Auditable.equalCellsCorrect
#print axioms Auditable.equalCellsCorrect

#modelClosureOfType Auditable.stockmeyerCorrect
#print axioms Auditable.stockmeyerCorrect

#surplusIn Auditable.Model from Auditable.finalAudit Auditable.equalCellsCorrect
  Auditable.stockmeyerCorrect
