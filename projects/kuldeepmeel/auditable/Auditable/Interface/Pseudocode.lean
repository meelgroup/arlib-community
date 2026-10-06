import Auditable.Interface.Encoding

/-!
# Pseudocode: `AFCounter` and `CountAuditor` as mathematics

Algorithm algo:pigeons (`AFCounter`, combined.tex:23-52) and Algorithm algo:lonely-audit
(`CountAuditor`, finalaudit.tex:17-29) written step by step as plain values. There is one
declaration per step of the restatement's `algorithmTranscript`. The assembled answers
are `result F` (the certificate) and `verdict F K` (the auditor's verdict). `result` is
*definitionally* `Interface.afCounterSpec` (`result_eq_afCounterSpec`, by `rfl`), and
`verdict` agrees with `Interface.countAuditorSpec` up to reassociating one `∧`
(`verdict_eq_countAuditorSpec`). So the interface has one pseudocode answer per
algorithm, not two that could drift apart. This file only spells each one out line by
line against its listing.

Nothing here is a claim about the program. The equations
`(Program.afCounter F).val = result F` and `(Program.countAuditor F K).val = verdict F K`
are the bridge, and they belong to the next pass (`Interface/ProgramModel.lean`).

## Why there are two definitions of each algorithm

`Program.afCounter` / `Program.countAuditor` (`Model/Program.lean`) and `result` /
`verdict` here compute the same answers. Neither is dead weight, and computability is
not the reason: everything on this side is noncomputable, and it is never run.

* **The program is a charged term.** It is a `Charged Op Cell` value: an answer sealed
  together with the tally that produced it. That tally is the paper's resource claim:
  how many `Σ₂ᴾ` calls the auditor makes, and how many quantified variables the call
  carries (`Op.sigma2Var`, read off `sigma2Oracle (auditQuery F' K)`). The expensive
  operations *are* the iterations `for m = 1 to n'` with one oracle query per round, and
  the single merged query whose prefix is counted. So the program has to hold each loop
  as a loop, in order, with its `break` realised operationally by
  `Charged.foldlWhile` (the stock loop even carries an `Option` register so that the
  rounds after the first success cost nothing). It also has to hold the audit query as
  syntax (`auditQuery`, a `BForm`) so that its prefix can be counted. That is the right
  shape for counting, and the wrong shape for reasoning about an answer. Two charged
  terms with the same answer but different histories are different terms, so `Charged`
  is not extensional in the answer.
* **The pseudocode is the answer only.** The correctness argument uses, of the counter,
  only *which* `m` each loop stops at (`c_low` is one below the first failing holes
  check, `c_high` is the first succeeding stock check), with the witnesses found there.
  `holesBreak` and `stockBreak` state that directly as `List.find?` over
  `List.range' 1 n'`, so the `find?` lemmas of core and Mathlib give "first" with no
  state machine, no register and no seal. Of the auditor it uses only the *meaning* of
  the oracle's answer: `poscheck` is `stockWith`, `negcheck` is `holesWith`, as
  propositions about `sol F'`, which is a `Finset`. That the program's one syntactic
  query `auditQuery F' K` holds exactly when `mergedCheck F K` does is the
  encoding-correctness claim the bridge has to prove.

There is no sealed dictionary in either algorithm: the registers are plain values, and
nothing in either run holds a set in an order the argument depends on. So the quotient
the analysis needs is not `Finset`-of-a-roster. It is the one above: each charged loop
reduced to the index it stops at, and the charged query reduced to the proposition it
encodes. No `PMF` is needed either, because neither algorithm draws anything
(`Model/Run.lean`). The random hashes of lm:holesexist and lm:stockexist live in their
proofs.

**No meter.** Nothing here counts oracle calls or query variables. They are
`Charged.cost` of the two programs and stay on the program side.

## Correspondence ledger: `AFCounter` (`algorithmTranscript.steps`, AFC-*)

| Step | Paper (combined.tex) | Pseudocode | Program (`Model/Program.lean`) |
|---|---|---|---|
| AFC-1 | `c_low ← 0; c_high ← n'; n' ← n log n; CntEst ← 0` | `nPrime n`; `c_low ← 0` is the `m − 1` of `holesResult` at `m = 1`; `c_high ← n'` is `stockDefault`; `CntEst ← 0` omitted (dead store, AFC-18 overwrites it) | `nPrime n`; `emptyHolesReg`; the `getD` default in `afCounter` |
| AFC-2 | `F' ← MakeCopies(F, log n)` | `formulaCopies` (= `Interface.fPrime`) | `makeCopies F (copies n)` in `afCounter` |
| AFC-3 | `hashassgn_stock ← ∅; hashassgn_holes ← ∅` | no value: the witnesses are read at the break index (`holesWitnessAt`, `stockWitnessAt`) | `emptyHolesReg`, `none` |
| AFC-4 | `for m = 1 to n'` | `loopRange` | `List.range' 1 (nPrime n)` |
| AFC-5 (line:low-qbf-check) | `(assign, ret) ← 3QBFCheck(φ_holes^{F'}(m))` | `holesRet` | `holesOracle` in `holesStep` |
| AFC-6..8 (line:low-check) | `if ret == 0 then c_low = m − 1; break` | `holesFails`, `holesBreak`, and the `some m` branch of `holesResult` | the `none => pure none` branch of `holesStep` |
| AFC-9 | `hashassgn_holes ← assign` | `holesWitnessAt` | the `some hs => pure (some ⟨m, hs⟩)` branch of `holesStep` |
| AFC-10 (no break) | (loop ends) | the `none` branch of `holesResult`: `c_low = n'` (**Deviation 1**) | the register after the full fold |
| AFC-11 | `for m' = 1 to n'` | `loopRange` | `List.range' 1 (nPrime n)` |
| AFC-12 (line:high-qbf-check) | `(assign, ret) ← 2QBFCheck(φ_stock^{F'}(m'))` | `stockRet` | `stockOracle` in `stockStep` |
| AFC-13..16 (line:high-check) | `if ret == 1 then c_high = m'; hashassgn_stock ← assign; break` | `stockSucceeds`, `stockBreak`, `stockWitnessAt`, the `some m` branch of `stockResult` | the `none` branch of `stockStep`, then `some _ => pure none` |
| AFC-17 (no break) | (loop ends) | `stockDefault` (**Deviation 2**: `n'` identity hashes) | `stock.getD ⟨nPrime n, …⟩` |
| AFC-18 | `CntEst ← 2^{c_high / log n}` | `cntEst` (real-valued, a read-off) | not computed: `estimate` is noncomputable |
| AFC-19 | `return (CntEst, c_low, c_high, …)` | `result` | the final `pure` of `afCounter` |

## Correspondence ledger: `CountAuditor` (AUD-*)

| Step | Paper (finalaudit.tex) | Pseudocode | Program |
|---|---|---|---|
| AUD-1 | `poscheck ← 0; negcheck ← 0` | omitted (no-op) | omitted |
| AUD-2 (line:zconpcheck) | `poscheck ← CoNPCheck(φ_stock^{F'}(c_high)[h ← hashassgn_stock])` | `poscheck` (isolation semantics, `stockWith`) | `stockPart` of `auditQuery` |
| AUD-3 (line:zconncheck) | `negcheck ← 2QBFCheck(φ_holes^{F'}(c_low)[h ← hashassgn_holes])` | `negcheck`, all `c_low + 1` hashes (**Deviation 4**) | `holesPart` of `auditQuery` |
| AUD-merged (l. 107, 136) | "combined and answered using a single `Σ₂ᴾ` oracle query" | `mergedCheck = poscheck ∧ negcheck` | the one `sigma2Oracle (auditQuery F' K)` |
| AUD-4 (line:zequalcheck) | `if (poscheck ∧ negcheck) ∧ c_high − c_low ≤ 7 then return Verified` | `gapCheck`, `verdict` | `natLe K.chigh (K.clow + 7)` and the final `if` |

`CntEst` is never read by the auditor (**Deviation 5**); `verdict` takes the certificate
`K : Cert n'`, which carries none.

The transcript and the program agree; no `MODEL:` gap was found. The program's five
deviations from the listings (its module docstring) are the transcript's
`omissionsOrChoices`, and the pseudocode follows the transcript on each: `c_low := n'`
when the holes loop never breaks, `c_high := n'` with identity hashes when the stock loop
never succeeds (unreachable for `n' ≥ 1`), the two auditor calls merged, all `c_low + 1`
holes hashes substituted, `CntEst` recomputed.

Two things the bridge and analysis must supply, recorded here so nobody mistakes them
for gaps in this file:

* The oracles' answers `holesRet` / `stockRet` are the program's exhaustive searches
  over `allHashTuples`. That `holesRet G m = none ↔ ¬ ∃ hs, holesWith G m hs` (and
  likewise for stock) is a fact about that enumeration, for the analysis.
* At index `0` the program keeps `emptyHolesReg`'s hash, while `holesWitnessAt G 0`
  falls back to `zeroHash`. `AffHash N 0` has exactly one member, so the two agree; the
  bridge proves it.

Departures from the paper inherited from `Model/Prelude.lean` and recorded there:
`φ_stock` is the isolation predicate (stock.tex:13-14), not the display at stock.tex:4;
`log n` is `Nat.clog 2 n`; the hash family is affine GF(2).
-/

set_option autoImplicit false

namespace Auditable.Interface.Pseudocode

open Auditable.Model.Operations
open Auditable.Program

noncomputable section

/-! ## `AFCounter` -/

/-- **AFC-2** `F' ← MakeCopies(F, log n)` (combined.tex:29, stock.tex:106-111): `⌈log₂ n⌉`
copies of `F` on disjoint variable blocks, a CNF over `n' = nPrime n` variables. -/
abbrev formulaCopies {n : ℕ} (F : CNF n) : CNF (nPrime n) := fPrime F

/-- **AFC-4 / AFC-11** `for m = 1 to n'`: the loop counter's values in the order both loops
visit them, `[1, 2, …, N]`. -/
def loopRange (N : ℕ) : List ℕ := List.range' 1 N

/-- **AFC-5** (line:low-qbf-check) `(assign, ret) ← 3QBFCheck(φ_holes^{G}(m))`: the oracle's
answer at `m`. `some assign` is `ret = 1` with its `m + 1` hashes, `none` is `ret = 0`. The
pseudocode reads it for free; the program pays one `holesQuery` for it. -/
def holesRet {N : ℕ} (G : CNF N) (m : ℕ) : Option (Fin (m + 1) → AffHash N m) :=
  holesAnswer G m

/-- **AFC-6** (line:low-check) `if ret == 0`: whether the holes check at `m` failed. A test
of the answer, as in the program. -/
def holesFails {N : ℕ} (G : CNF N) (m : ℕ) : Bool := (holesRet G m).isNone

/-- **AFC-7..8** `break`: the holes loop stops at the **first** `m ∈ [1, N]` whose check
failed, or runs out (`none`). -/
def holesBreak {N : ℕ} (G : CNF N) : Option ℕ := (loopRange N).find? (holesFails G)

/-- **AFC-9** `hashassgn_holes ← assign`: the witness recorded at index `m`, the last round
whose check succeeded. The fallback is never what the honest run reads (see the module
docstring for index `0`). -/
def holesWitnessAt {N : ℕ} (G : CNF N) (m : ℕ) : Fin (m + 1) → AffHash N m :=
  (holesRet G m).getD fun _ => zeroHash N m

/-- **AFC-4..10** `(c_low, hashassgn_holes)`: `c_low = m − 1` for the first failing `m`
(AFC-7), or `c_low = N` if none fails (**Deviation 1**, the prose's "largest `m`",
combined.tex:20), with the witness found at `c_low`. -/
def holesResult {N : ℕ} (G : CNF N) : HolesReg N :=
  match holesBreak G with
  | some m => ⟨m - 1, holesWitnessAt G (m - 1)⟩
  | none => ⟨N, holesWitnessAt G N⟩

/-- **AFC-12** (line:high-qbf-check) `(assign, ret) ← 2QBFCheck(φ_stock^{G}(m'))`: the
oracle's answer at `m'`, with its `m'` hashes on `some`. -/
def stockRet {N : ℕ} (G : CNF N) (m : ℕ) : Option (Fin m → AffHash N m) :=
  stockAnswer G m

/-- **AFC-13** (line:high-check) `if ret == 1`: whether the stock check at `m'` succeeded. -/
def stockSucceeds {N : ℕ} (G : CNF N) (m : ℕ) : Bool := (stockRet G m).isSome

/-- **AFC-14..16** `c_high = m'; break`: the stock loop stops at the **first** `m' ∈ [1, N]`
whose check succeeded, or runs out (`none`). -/
def stockBreak {N : ℕ} (G : CNF N) : Option ℕ := (loopRange N).find? (stockSucceeds G)

/-- **AFC-15** `hashassgn_stock ← assign`: the witness recorded at the succeeding round `m`.
The fallback is never read, since `stockBreak` only returns an `m` whose answer is
`some`. -/
def stockWitnessAt {N : ℕ} (G : CNF N) (m : ℕ) : Fin m → AffHash N m :=
  (stockRet G m).getD fun _ => zeroHash N m

/-- **AFC-11..17** `(c_high, hashassgn_stock)`: the first succeeding `m'` with its witness,
or `stockDefault N` (`c_high = N` with identity hashes, **Deviation 2**) if none
succeeds. -/
def stockResult {N : ℕ} (G : CNF N) : Σ m : ℕ, (Fin m → AffHash N m) :=
  match stockBreak G with
  | some m => ⟨m, stockWitnessAt G m⟩
  | none => stockDefault N

/-- **AFC-19** `return (CntEst, c_low, c_high, hashassgn_stock, hashassgn_holes)`
(combined.tex:51): **what Algorithm algo:pigeons answers**, as pseudocode. `CntEst` is
not a field; it is the read-off `cntEst`. -/
def result {n : ℕ} (F : CNF n) : Cert (nPrime n) :=
  { clow := (holesResult (formulaCopies F)).1, chigh := (stockResult (formulaCopies F)).1,
    hstock := (stockResult (formulaCopies F)).2, hholes := (holesResult (formulaCopies F)).2 }

/-- **AFC-18** `CntEst ← 2^{c_high / log n}` (combined.tex:48): the real number the counter
reports, read off its certificate. -/
def cntEst {n : ℕ} (F : CNF n) : ℝ := estimate (copies n) (result F).chigh

/-- The step-by-step pseudocode is the interface answer of `Interface/Encoding.lean`. -/
theorem result_eq_afCounterSpec {n : ℕ} (F : CNF n) : result F = afCounterSpec F := rfl

/-! ## `CountAuditor` -/

/-- **AUD-2** (line:zconpcheck) `poscheck ← CoNPCheck(φ_stock^{F'}(c_high)[h ← hashassgn_stock])`:
every solution of `F'` is isolated by one of the certificate's stock hashes (isolation
semantics, `stockWith`). -/
abbrev poscheck {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) : Prop :=
  stockWith (formulaCopies F) K.chigh K.hstock

/-- **AUD-3** (line:zconncheck) `negcheck ← 2QBFCheck(φ_holes^{F'}(c_low)[h ← hashassgn_holes])`:
every cell of `{0,1}^{c_low}` is hit by a solution of `F'` under one of the certificate's
`c_low + 1` holes hashes (**Deviation 4**: all `c_low + 1` substituted). -/
abbrev negcheck {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) : Prop :=
  holesWith (formulaCopies F) K.clow K.hholes

/-- **AUD-merged** (finalaudit.tex:107, 136): what the auditor's single `Σ₂ᴾ` query asks,
`poscheck ∧ negcheck`. The program asks it as the syntactic query
`auditQuery (fPrime F) K`; that the query holds exactly when this does is the bridge's
encoding-correctness claim. -/
abbrev mergedCheck {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) : Prop :=
  poscheck F K ∧ negcheck F K

/-- **AUD-4** (line:zequalcheck), the gap test `c_high − c_low ≤ 7`, without truncated
subtraction. -/
abbrev gapCheck {N : ℕ} (K : Cert N) : Prop := K.chigh ≤ K.clow + 7

/-- **AUD-4** `if (poscheck ∧ negcheck) ∧ c_high − c_low ≤ 7 then return Verified`
(finalaudit.tex:27): **what Algorithm algo:lonely-audit answers**, as pseudocode. The
listing has no `else`; falling through is `rejected`. -/
def verdict {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) : Verdict :=
  if mergedCheck F K ∧ gapCheck K then Verdict.verified else Verdict.rejected

/-- The step-by-step pseudocode is the interface answer of `Interface/Encoding.lean`, which
writes the same test as `A ∧ B ∧ C` rather than `(A ∧ B) ∧ C`. -/
theorem verdict_eq_countAuditorSpec {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) :
    verdict F K = countAuditorSpec F K :=
  if_congr and_assoc rfl rfl

end

end Auditable.Interface.Pseudocode
