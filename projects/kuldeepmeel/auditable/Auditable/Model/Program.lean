import Auditable.Model.Operations
import Auditable.Meta.CostSeal
import Auditable.Meta.ModelClosure

/-!
# `AFCounter` (Algorithm algo:pigeons) and `CountAuditor` (Algorithm algo:lonely-audit)

Both algorithms as charged programs in the currency of `Model/Operations.lean`.
Both are deterministic: the paper's random hashes appear only in existence proofs
(lm:holesexist, lm:stockexist), never in either algorithm.

## Correspondence ledger: `AFCounter` (combined.tex:23-52) → `afCounter`

| line | paper | Lean |
|---|---|---|
| AFC-1 | `c_low ← 0; c_high ← n'; n' ← n log n; CntEst ← 0` | `nPrime n`; the registers below |
| AFC-2 | `F' ← MakeCopies(F, log n)` | `makeCopies F (copies n)` (uncharged) |
| AFC-3 | `hashassgn_stock ← ∅; hashassgn_holes ← ∅` | `emptyHolesReg`, `none` |
| AFC-4..10 | `for m = 1 to n'`: `3QBFCheck(φ_holes(m))`; on `ret = 0`: `c_low = m − 1`, break; else `hashassgn_holes ← assign` | `Charged.foldlWhile (holesStep F')` over `List.range' 1 n'` |
| AFC-11..17 | `for m' = 1 to n'`: `2QBFCheck(φ_stock(m'))`; on `ret = 1`: `c_high = m'`, `hashassgn_stock ← assign`, break | `Charged.foldlWhile (stockStep F')` over `List.range' 1 n'` |
| AFC-18 | `CntEst ← 2^{c_high / log n}` | not here: `estimate` in `Model/Prelude.lean` (real-valued) |
| AFC-19 | `return (CntEst, c_low, c_high, …)` | the final `pure` of a `Cert` |

The holes register holds `⟨m, hs⟩`, the last index whose check succeeded and its
witness. When the loop breaks at the first failing `m` the register holds index
`m − 1`, which is the listing's `c_low = m − 1`, with that iteration's witness.

**Deviation 1 (paper defect, disclosed).** When no `m ∈ [1, n']` fails, the listing
leaves `c_low` at its initial `0` while `hashassgn_holes` holds the `m = n'`
witness; for `F ≡ True` the auditor then rejects the honest output. Here the
register then holds `⟨n', witness at n'⟩`, i.e. `c_low = n'`, as the prose says
("`c_low` is the largest `m` for which `φ_holes(m)` is True", combined.tex:20).
This is the register semantics above, not a separate case.

**Deviation 2 (unreachable default).** If the stock loop never succeeds,
the listing returns `c_high = n'` with an empty `hashassgn_stock`, which has the
wrong type. Here the default is `c_high = n'` with `n'` identity hashes. With
`n' ≥ 1` the default is never taken (the identity tuple isolates every point, so
the check at `m' = n'` succeeds); with `n' = 0` the loop is empty and `c_high = 0`.

The stock loop's register is `Option`: once a witness is recorded, the next round
stops at no cost (`pure none`), so the tally stops at the first success, as the
listing's `break` does.

Both loops are the listing's first-failure / first-success control flow, not
`Nat.find` / `Nat.findGreatest` on the predicates; no monotonicity in `m` is used
or assumed.

## Correspondence ledger: `CountAuditor` (finalaudit.tex:17-29) → `countAuditor`

| line | paper | Lean |
|---|---|---|
| AUD-1 | `poscheck ← 0; negcheck ← 0` | omitted (no-op) |
| AUD-2 | `poscheck ← CoNPCheck(φ_stock(c_high)[h ← hashassgn_stock])` | `stockPart` of `auditQuery` |
| AUD-3 | `negcheck ← 2QBFCheck(φ_holes(c_low)[h ← hashassgn_holes])` | `holesPart` of `auditQuery`, all `c_low + 1` hashes |
| AUD-merged | "combined and answered using a single `Σ₂ᴾ` oracle query" (finalaudit.tex:107, 136) | one `sigma2Oracle (auditQuery F' K)` |
| AUD-4 | `if poscheck ∧ negcheck ∧ c_high − c_low ≤ 7 then return Verified` | `natLe K.chigh (K.clow + 7)` and the final `if` |

**Deviation 3 (two calls merged).** The listing shows two oracle calls; the
theorem's proof merges them into one forall-exists query, and so does the
program: exactly one `sigma2Oracle` call.

**Deviation 4 (`h_{c_low+1}` substituted).** `φ_holes(c_low)` has `c_low + 1`
hashes (combined.tex:9); finalaudit.tex:23 substitutes `h_1 … h_{c_low}`. All
`c_low + 1` are substituted.

**Deviation 5 (`CntEst` not trusted).** The auditor never reads a supplied
`CntEst`; the certificate has none, and the estimate is recomputed from `c_high`.

**Encoding of `poscheck` (the main finding).** `φ_stock` has the isolation
semantics `∀ z₁ ∃ i ∀ z₂` (see `stockWith`). Its quantifier-free forall-exists
form uses `⋁ᵢ ∀ y. Pᵢ(y) ≡ ∀ y₁ … y_c. ⋁ᵢ Pᵢ(yᵢ)`, so the universal block has one
copy `z₂⁽ⁱ⁾` per stock hash:

`∀ z₁ z₂⁽¹⁾ … z₂⁽ᶜʰⁱᵍʰ⁾ α ∃ z.
  [F'(z₁) → ⋁ᵢ (F'(z₂⁽ⁱ⁾) ∧ z₂⁽ⁱ⁾ ≠ z₁ → hᵢ(z₂⁽ⁱ⁾) ≠ hᵢ(z₁))] ∧ ⋁_{i ≤ c_low} (F'(z) ∧ hᵢ(z) = α)`.

Its size is `(c_high + 2) · n' + c_low`. The paper's count (one `z₂`, size
`3n' + c_low`) is correct only for the pairwise reading of stock.tex:4, under
which soundness fails.

Variable layout: universal `Fin (n' + c_high · n' + c_low)` is `z₁`, then the
`z₂⁽ⁱ⁾` blocks (`finProdFinEquiv (i, j)`), then `α`; existential `Fin n'` is `z`.
-/

set_option autoImplicit false

namespace Auditable.Program

open Auditable
open Auditable.Model.Operations
open Arlib.Computation (Charged)

/-! ## `AFCounter` -/

/-- The holes loop's register: the last index `m` whose `φ_holes` check succeeded,
with its `m + 1` hashes (`c_low` and `hashassgn_holes`). -/
abbrev HolesReg (N : ℕ) : Type := Σ m : ℕ, (Fin (m + 1) → AffHash N m)

/-- The stock loop's register: `none` until a check succeeds, then that index with
its hashes (`c_high` and `hashassgn_stock`). -/
abbrev StockReg (N : ℕ) : Type := Option (Σ m : ℕ, (Fin m → AffHash N m))

/-- AFC-1/AFC-3: `c_low = 0` with the (unique) hash into `{0,1}^0`. -/
def emptyHolesReg (N : ℕ) : HolesReg N :=
  ⟨0, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩

/-- AFC-4..10, one round `m`: ask `3QBFCheck(φ_holes^{G}(m))`; on a witness record
`⟨m, assign⟩` and continue, otherwise break (keeping `⟨m − 1, …⟩`). -/
def holesStep {N : ℕ} (G : CNF N) (_reg : HolesReg N) (m : ℕ) :
    Charged Op Cell (Option (HolesReg N)) := do
  let ret ← holesOracle G m
  match ret with
  | some hs => pure (some ⟨m, hs⟩)
  | none => pure none

/-- AFC-11..17, one round `m'`: if a witness is already recorded, break; otherwise
ask `2QBFCheck(φ_stock^{G}(m'))` and record `⟨m', assign⟩` on success. -/
def stockStep {N : ℕ} (G : CNF N) (reg : StockReg N) (m : ℕ) :
    Charged Op Cell (Option (StockReg N)) :=
  match reg with
  | some _ => pure none
  | none => do
      let ret ← stockOracle G m
      match ret with
      | some hs => pure (some (some ⟨m, hs⟩))
      | none => pure (some none)

/-- The identity map `{0,1}^N → {0,1}^N` as an affine hash (`A = I`, `b = 0`). Used
only for the stock loop's unreachable default (Deviation 2). -/
def identityHash (N : ℕ) : AffHash N N :=
  ⟨fun i j => decide (i = j), fun _ => false⟩

/-- **`AFCounter(F)`** (Algorithm algo:pigeons, combined.tex:23-52). Returns the
certificate `(c_low, c_high, hashassgn_stock, hashassgn_holes)`; `CntEst` is the
read-off `estimate (copies n) c_high`. -/
def afCounter {n : ℕ} (F : CNF n) : Charged Op Cell (Cert (nPrime n)) := do
  let F' : CNF (nPrime n) := makeCopies F (copies n)
  let holes ← Charged.foldlWhile (holesStep F') (List.range' 1 (nPrime n))
    (emptyHolesReg (nPrime n))
  let stock ← Charged.foldlWhile (stockStep F') (List.range' 1 (nPrime n)) none
  let high : Σ m : ℕ, (Fin m → AffHash (nPrime n) m) :=
    stock.getD ⟨nPrime n, fun _ => identityHash (nPrime n)⟩
  pure { clow := holes.1, chigh := high.1, hstock := high.2, hholes := holes.2 }

/-! ## The audit query -/

/-- `⋀ fs`. -/
def bAll {V : Type} (fs : List (BForm V)) : BForm V := fs.foldr BForm.and (BForm.const true)

/-- `⋁ fs`. -/
def bAny {V : Type} (fs : List (BForm V)) : BForm V := fs.foldr BForm.or (BForm.const false)

/-- `f → g`. -/
def bImp {V : Type} (f g : BForm V) : BForm V := BForm.or (BForm.not f) g

/-- `f ↔ g`. -/
def bIff {V : Type} (f g : BForm V) : BForm V := BForm.not (BForm.xor f g)

/-- `G(z)`, with `G`'s variable `v` read as the query variable `z v`. -/
def cnfForm {N : ℕ} {V : Type} (G : CNF N) (z : Fin N → V) : BForm V :=
  bAll (G.map fun c => bAny (c.map fun l =>
    if l.pos then BForm.var (z l.var) else BForm.not (BForm.var (z l.var))))

/-- Output bit `i` of `h(z)`, mirroring `AffHash.apply`:
`b i ⊕ ⨁ⱼ (A i j ∧ z j)` with the coefficients as constants. -/
def hashBitForm {N m : ℕ} {V : Type} (h : AffHash N m) (z : Fin N → V) (i : Fin m) :
    BForm V :=
  BForm.xor (BForm.const (h.b i))
    ((List.finRange N).foldl
      (fun acc j => BForm.xor acc (BForm.and (BForm.const (h.A i j)) (BForm.var (z j))))
      (BForm.const false))

/-- `x ≠ y` for two bit-vectors of formulas. -/
def neqForm {k : ℕ} {V : Type} (x y : Fin k → BForm V) : BForm V :=
  bAny ((List.finRange k).map fun i => BForm.xor (x i) (y i))

/-- `x = y` for two bit-vectors of formulas. -/
def eqForm {k : ℕ} {V : Type} (x y : Fin k → BForm V) : BForm V :=
  bAll ((List.finRange k).map fun i => bIff (x i) (y i))

/-- The merged query (AUD-merged) on `G = F'` and certificate `K`. Universal:
`z₁` (`N`), `z₂⁽ⁱ⁾` for `i < c_high` (`c_high · N`), `α` (`c_low`); existential:
`z` (`N`). Matrix: AUD-2 ∧ AUD-3, with every hash substituted as constants. -/
def auditQuery {N : ℕ} (G : CNF N) (K : Cert N) : Pi2Query :=
  let z₁ : Fin N → Fin (N + K.chigh * N + K.clow) ⊕ Fin N := fun j =>
    Sum.inl (Fin.castAdd K.clow (Fin.castAdd (K.chigh * N) j))
  let z₂ : Fin K.chigh → Fin N → Fin (N + K.chigh * N + K.clow) ⊕ Fin N := fun i j =>
    Sum.inl (Fin.castAdd K.clow (Fin.natAdd N (finProdFinEquiv (i, j))))
  let α : Fin K.clow → Fin (N + K.chigh * N + K.clow) ⊕ Fin N := fun t =>
    Sum.inl (Fin.natAdd (N + K.chigh * N) t)
  let z : Fin N → Fin (N + K.chigh * N + K.clow) ⊕ Fin N := fun j => Sum.inr j
  -- AUD-2: φ_stock(c_high)[h ← hashassgn_stock], isolation semantics
  let stockPart := bImp (cnfForm G z₁) (bAny ((List.finRange K.chigh).map fun i =>
    bImp
      (BForm.and (cnfForm G (z₂ i))
        (neqForm (fun j => BForm.var (z₂ i j)) (fun j => BForm.var (z₁ j))))
      (neqForm (hashBitForm (K.hstock i) (z₂ i)) (hashBitForm (K.hstock i) z₁))))
  -- AUD-3: φ_holes(c_low)[h ← hashassgn_holes], all c_low + 1 hashes
  let holesPart := bAny ((List.finRange (K.clow + 1)).map fun i =>
    BForm.and (cnfForm G z)
      (eqForm (hashBitForm (K.hholes i) z) (fun t => BForm.var (α t))))
  { nU := N + K.chigh * N + K.clow, nE := N, matrix := BForm.and stockPart holesPart }

/-! ## `CountAuditor` -/

/-- **`CountAuditor(F, K)`** (Algorithm algo:lonely-audit, finalaudit.tex:17-29),
with its two oracle calls merged into the one `Σ₂ᴾ` query `auditQuery F' K`. -/
def countAuditor {n : ℕ} (F : CNF n) (K : Cert (nPrime n)) : Charged Op Cell Verdict := do
  let F' : CNF (nPrime n) := makeCopies F (copies n)
  let answer ← sigma2Oracle (auditQuery F' K)
  let gapOk ← natLe K.chigh (K.clow + 7)
  if answer && gapOk then pure Verdict.verified else pure Verdict.rejected

end Auditable.Program

#programSeal Auditable.Program
#executableModule Auditable.Model.Program
#surplusIn Auditable.Model.Program from Auditable.Program.afCounter
  Auditable.Program.countAuditor

/-! ## `EqualCellsCounter` (Algorithm algo:smallcells, thm:intermediate)

Added beside `afCounter` and `countAuditor`, which are unchanged. It is charged in
its own currency `CellsOp` (`Model/Operations.lean`), whose one primitive is
`3QBFCheck(φ_Cells^{⟨F,ℓ,u⟩}(m))`, so it calls no `Op` primitive at all.

### Correspondence ledger: `EqualCellsCounter` (bgp.tex:76-98) → `equalCellsCounter`

The listing's line numbers below are the ones `Model/Prelude.lean` and
`Model/Theorem.lean` cite; the listing itself is not in this repository.

| line | paper | Lean |
|---|---|---|
| 1-2 | `u ← 16384 n; ℓ ← 1024 n` | `cellsHigh n`, `cellsLow n` |
| 3 | `hashassgn_cells ← 0` | the register's `none` |
| loop | `for m = 1 to n` | `Charged.foldlWhile (cellsStep bits F)` over `List.range' 1 n` |
| bgp.tex:84 | `(ret, assign) ← 3QBFCheck(φ_Cells^{⟨F,ℓ,u⟩}(m))` | `cellsOracle bits F (cellsLow n) (cellsHigh n) m` |
| if-branch | on `ret = 1`: `hashassgn_cells ← assign`, `break` | register `(m, some c)`; the next round stops at no cost |
| 11 | `CntEst ← ℓ · 2^m` | `cellsLow n * 2 ^ m` (uncharged arithmetic) |
| 12 | `return (CntEst, hashassgn_cells)` | the final `pure` of a `CellsOut` |

The register is `(m, hashassgn_cells)`: the last round that ran and, once one has
succeeded, its witness. As in the stock loop of `afCounter`, a recorded witness makes
the next round stop at no cost (`pure none`), so the tally stops at the first
success.

**Deviation 6 (`break` inside the `if`).** Read literally, the listing's `break`
ends the loop after round `m = 1` whatever the oracle answered (so `CntEst = 2048 n`
on every `F` whose check at `m = 1` fails). The proof of thm:intermediate searches
for the first `m` whose check passes, so the `break` is taken only on success.

**Deviation 7 (no-success default).** If no round succeeds, the loop variable is
left at its last value `m = n` (and `hashassgn_cells` at its initial value, here
`none`), so `CntEst = ℓ · 2^n`. With `n = 0` the loop is empty and `m = 0 = n`.
The paper does not say what the algorithm returns in this case.
-/

namespace Auditable.Program

open Auditable
open Auditable.Model.Operations
open Arlib.Computation (Charged)

/-- The `EqualCellsCounter` loop's register: the last round `m` that ran, and
`hashassgn_cells` (`none` until a check succeeds, then that round's witness). -/
abbrev CellsReg (K : Type) (n : ℕ) : Type := ℕ × Option (CellHash K n)

/-- One round `m` of `EqualCellsCounter`'s loop: if a witness is already recorded,
break; otherwise ask `3QBFCheck(φ_Cells^{⟨F,ℓ,u⟩}(m))` (bgp.tex:84) and record
`(m, assign)` on success, `(m, none)` on failure. -/
def cellsStep {K : Type} [Field K] [FinEnum K] {n : ℕ} (bits : K ≃ (Fin n → Bool))
    (F : CNF n) (reg : CellsReg K n) (m : ℕ) :
    Charged CellsOp Cell (Option (CellsReg K n)) :=
  match reg.2 with
  | some _ => pure none
  | none => do
      let ret ← cellsOracle bits F (cellsLow n) (cellsHigh n) m
      match ret with
      | some c => pure (some (m, some c))
      | none => pure (some (m, none))

/-- **`EqualCellsCounter(F)`** (Algorithm algo:smallcells, bgp.tex:76-98), with
`ℓ = 1024 n`, `u = 16384 n`, hashes from `H(n, m, n)` over the field `K` encoded by
`bits`. Returns the stopping round `m`, `CntEst = ℓ · 2^m` and `hashassgn_cells`. -/
def equalCellsCounter {K : Type} [Field K] [FinEnum K] {n : ℕ}
    (bits : K ≃ (Fin n → Bool)) (F : CNF n) : Charged CellsOp Cell (CellsOut K n) := do
  let reg ← Charged.foldlWhile (cellsStep bits F) (List.range' 1 n) (0, none)
  pure { m := reg.1, cntEst := cellsLow n * 2 ^ reg.1, hcells := reg.2 }

end Auditable.Program

#programSeal Auditable.Program
#executableModule Auditable.Model.Program
#surplusIn Auditable.Model.Program from Auditable.Program.afCounter
  Auditable.Program.countAuditor Auditable.Program.equalCellsCounter

/-! ## `Stock` (Algorithm algo:stock, Theorem [Stockmeyer])

Added beside `afCounter`, `countAuditor` and `equalCellsCounter`, which are unchanged.
`Stock`'s one loop is `AFCounter`'s stock loop (AFC-11..17): the same step
`stockStep`, the same oracle `stockOracle` (one `Op.stockQuery` per round), the same
fold over `List.range' 1 n'` from the empty register. It makes no `holesQuery` and no
`sigma2Query` call.

### Correspondence ledger: `Stock` (stock.tex:84-103) → `stockCounter`

| line | paper | Lean |
|---|---|---|
| STK-1 | `v ← 0; hashassgn_stock ← {}; CntEst ← 0` | register `none`; default `⟨0, empty tuple⟩` |
| STK-2 | `F' ← MakeCopies(F, log n)` | `makeCopies F (copies n)` (uncharged) |
| STK-3 | `for m = 1 to n log n` | `Charged.foldlWhile (stockStep F')` over `List.range' 1 (nPrime n)` |
| STK-4 | `(ret, assign) ← 2QBFCheck(φ_stock^{F'}(m))` | `stockOracle F' m` (one `stockQuery`) |
| STK-5..7 | `if ret == 1: v = m; hashassgn_stock = assign` | register `some ⟨m, hs⟩` |
| STK-8 | `break` | `stockStep`'s `some _ => pure none`: the fold stops value and tally |
| STK-9 | `CntEst = 2^{v / log n}` | not here: `estimate (copies n) v` in `Model/Prelude.lean` |
| STK-10 | `return (v, CntEst, hashassgn_stock)` | the final `pure` of a `StockOut` |

**Deviation 8 (`break` inside the `if`).** The listing puts `break` after `EndIf`
(stock.tex:97), so read literally the loop stops after `m = 1` whatever the oracle
answered: `v ∈ {0, 1}`, and the theorem is false (`n = 5`, `F = []`: `|sol F| = 32`,
`φ_stock^{F'}(1)` fails, so `v = 0` and `CntEst = 1 < 32 / 16`). The prose
(stock.tex:109-111, "searches for the first point (smallest value of `m`) where
`φ_stock^{F'}(i) = 1`") and the proof fix the reading modelled here: `break` only on
success, as in Deviation 6.

**Deviation 9 (no-success default).** If no round succeeds, `v` and
`hashassgn_stock` keep their initial values (STK-1): `v = 0` with the empty tuple,
which here is well-typed (unlike Deviation 2). With `n' ≥ 1` the default is never
taken (the identity tuple isolates every point at `m = n'`); with `n' = 0` the loop
is empty and `v = 0`. So `stockCounter`'s `v` agrees with `afCounter`'s `c_high` only
when `n' ≥ 1`.

The loop is first-success control flow, not `Nat.find`; the monotonicity
`φ_stock(i) ⇒ φ_stock(i + 1)` the prose asserts (stock.tex:111) is not used.
-/

namespace Auditable.Program

open Auditable
open Auditable.Model.Operations
open Arlib.Computation (Charged)

/-- **`Stock(F)`** (Algorithm algo:stock, stock.tex:84-103), with the `break` taken
only on success (Deviation 8). Returns `v` and `hashassgn_stock`; `CntEst` is the
read-off `estimate (copies n) v`. -/
def stockCounter {n : ℕ} (F : CNF n) : Charged Op Cell (StockOut (nPrime n)) := do
  let F' : CNF (nPrime n) := makeCopies F (copies n)
  let stock ← Charged.foldlWhile (stockStep F') (List.range' 1 (nPrime n)) none
  let w : Σ m : ℕ, (Fin m → AffHash (nPrime n) m) := stock.getD ⟨0, fun i => i.elim0⟩
  pure { v := w.1, hstock := w.2 }

end Auditable.Program

#programSeal Auditable.Program
#executableModule Auditable.Model.Program
#surplusIn Auditable.Model.Program from Auditable.Program.afCounter
  Auditable.Program.countAuditor Auditable.Program.equalCellsCounter
  Auditable.Program.stockCounter
