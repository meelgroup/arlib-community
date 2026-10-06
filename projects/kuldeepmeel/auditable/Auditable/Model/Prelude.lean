import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Vocabulary of the audit of `AFCounter` (thm:finalaudit)

What the theorem is stated in: CNF formulas and their solution counts, the
`MakeCopies` amplification, the affine GF(2) hash family, the two formulas the
auditor substitutes a certificate into (`φ_holes`, `φ_stock`), the certificate
itself, the syntactic forall-exists query sent to the `Σ₂ᴾ` oracle, and the
estimate `CntEst`.

## Encoding decisions, and why

* **Formulas are CNFs over a declared arity.** `CNF n` is a list of clauses over
  `Fin n`; an assignment is `Fin n → Bool`. `|sol F|` counts assignments of all
  `n` declared variables (prelim.tex:2-8 takes `n = |Vars(F)|`).
* **`log n` is `Nat.clog 2 n` (ceiling).** The paper never says how `log n` is
  rounded. The root-taking step of the proof needs `n ≤ 2 ^ k`: with floor and
  `12 ≤ n ≤ 15` one gets `k = 3`, and `128 · (c_low + 1)` can exceed `16 ^ 3`.
* **`φ_stock` has the isolation semantics** (`stockWith`: `∀ z₁ ∃ i ∀ z₂`), as the
  prose says (stock.tex:13-14, combined.tex:5) and as the proof of cl:stockup uses.
  The displayed formula at stock.tex:4 (`∀ z₁ ∀ z₂ ⋁ᵢ …`) says something else: read
  literally it is false for every satisfiable `F` (take `z₁ = z₂`), and with a
  `z₁ ≠ z₂` guard it says the joint hash map is injective on `sol F`, under which
  cl:stockup is false (`n = 4`, `m = 2`, `F ≡ True`, two block projections give
  `|sol| = 16 > m · 2 ^ m = 8`). The pairwise reading is not defined here.
* **`φ_holes(m)` carries `m + 1` hash functions** (combined.tex:9), so the
  certificate's holes witness has type `Fin (clow + 1) → AffHash N clow`. This
  corrects the off-by-one at finalaudit.tex:23, which substitutes only
  `h_1 … h_{c_low}`.
* **Hash family.** The paper's family `H(n, m, 2)` (prelim.tex:82-118) is a
  GF(2^max(n,m)) coefficient family. We use affine GF(2) maps `z ↦ A z ⊕ b`
  (`AffHash`). Soundness holds for arbitrary hash functions; completeness uses
  pairwise independence, the identity at `m = N`, and the constant maps, which this
  family has. Hashes are substituted constants in the audit query, so their
  bit-size does not enter the theorem.
* **The oracle query is syntax, not a Lean proposition.** `Pi2Query.matrix` is a
  quantifier-free `BForm`. Were it a `Prop`, the variable count would mean nothing:
  a semantic matrix can hide `∀ z₂` inside it, or ask for the answer outright with
  zero variables.
* **The estimate is recomputed, not carried.** `Cert` has no `CntEst` field; the
  auditor never checks a supplied one (finalaudit.tex:17-29), so the theorem speaks
  about `estimate (copies n) K.chigh = 2 ^ (c_high / k)`.

## Correspondence ledger

| paper | Lean |
|---|---|
| `F`, `sol(F)`, `\|sol F\|` (prelim.tex:2-8) | `CNF`, `CNF.eval`, `sol`, `solCount` |
| `log n`, `n' = n log n` (combined.tex:28-29) | `copies`, `nPrime` |
| `MakeCopies(F, log n)` (stock.tex:106-111) | `makeCopies` |
| `H(n', m, 2)` (prelim.tex:82-118) | `AffHash`, `AffHash.apply` |
| `φ_holes^{F'}(m)[h ← …]` (combined.tex:8-14) | `holesWith` |
| `φ_stock^{F'}(m)[h ← …]` (stock.tex:13-14) | `stockWith` (isolation; see above) |
| output `(c_low, c_high, hashassgn_stock, hashassgn_holes)` | `Cert` |
| `CntEst = 2^{c_high / log n}` (combined.tex:48) | `estimate` |
| `Verified` (finalaudit.tex:27) | `Verdict` |
| "single `Σ₂ᴾ` query" (finalaudit.tex:107, 136) | `Pi2Query`, `Pi2Query.holds` |
| audit complexity `r` (problem.tex:22-34) | `Pi2Query.size` |
-/

set_option autoImplicit false

namespace Auditable

/-! ## Vocabulary -/

/-- A literal over the variables `Fin n`: the variable and its polarity
(`pos = true` is the positive literal). -/
structure Lit (n : ℕ) where
  /-- The variable. -/
  var : Fin n
  /-- `true` for `x`, `false` for `¬x`. -/
  pos : Bool
  deriving DecidableEq

/-- A truth assignment to the variables `Fin n`. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- A CNF formula over `Fin n`: a conjunction of clauses, each a disjunction of
literals (prelim.tex:2). -/
abbrev CNF (n : ℕ) := List (List (Lit n))

/-- Whether `σ` satisfies `F`. -/
def CNF.eval {n : ℕ} (F : CNF n) (σ : Assignment n) : Bool :=
  F.all fun c => c.any fun l => σ l.var == l.pos

/-- `sol(F)`: the satisfying assignments of `F`. -/
def sol {n : ℕ} (F : CNF n) : Finset (Assignment n) :=
  Finset.univ.filter fun σ => F.eval σ = true

/-- `|sol(F)|`, the number the counter estimates. -/
def solCount {n : ℕ} (F : CNF n) : ℕ := (sol F).card

/-- `k = log n`, the number of copies `MakeCopies` makes, rounded **up**
(`Nat.clog 2 n`). Ceiling is what gives `n ≤ 2 ^ k`, which the constants `4` and
`16` of the theorem depend on; the paper leaves the rounding unstated. -/
def copies (n : ℕ) : ℕ := Nat.clog 2 n

/-- `n' = n · log n`, the number of variables of `F' = MakeCopies(F, log n)`, and
the upper end of both of `AFCounter`'s loops. -/
def nPrime (n : ℕ) : ℕ := n * copies n

/-- `MakeCopies(F, k)` (stock.tex:106-111): `k` copies of `F`, copy `j` on its own
block of fresh variables, conjoined. Variable `v` of copy `j` is
`finProdFinEquiv (v, j) : Fin (n * k)`. -/
def makeCopies {n : ℕ} (F : CNF n) (k : ℕ) : CNF (n * k) :=
  (List.finRange k).flatMap fun j =>
    F.map (List.map fun l => ⟨finProdFinEquiv (l.var, j), l.pos⟩)

/-- A member of the hash family `H(N, m, 2)`: the affine GF(2) map
`z ↦ A z ⊕ b` from `{0,1}^N` to `{0,1}^m`. -/
structure AffHash (N m : ℕ) where
  /-- The matrix `A`, row `i` column `j`. -/
  A : Fin m → Fin N → Bool
  /-- The offset `b`. -/
  b : Fin m → Bool
  deriving DecidableEq

/-- Apply an affine hash: output bit `i` is `b i ⊕ ⨁ⱼ (A i j ∧ z j)`. -/
def AffHash.apply {N m : ℕ} (h : AffHash N m) (z : Fin N → Bool) : Fin m → Bool :=
  fun i => xor (h.b i) ((List.finRange N).foldl (fun acc j => xor acc (h.A i j && z j)) false)

/-- `φ_holes^G(m)` with its `m + 1` hash functions substituted (combined.tex:8-14):
every cell `α ∈ {0,1}^m` is hit by some solution under some `hᵢ`. -/
def holesWith {N : ℕ} (G : CNF N) (m : ℕ) (hs : Fin (m + 1) → AffHash N m) : Prop :=
  ∀ α : Fin m → Bool, ∃ z : Assignment N, G.eval z = true ∧ ∃ i, (hs i).apply z = α

/-- `φ_stock^G(m)` with its `m` hash functions substituted, **isolation semantics**
(stock.tex:13-14, combined.tex:5): every solution `z₁` is the only solution in its
cell under some `hᵢ`. This is not the displayed formula at stock.tex:4; see the
module docstring. -/
def stockWith {N : ℕ} (G : CNF N) (m : ℕ) (hs : Fin m → AffHash N m) : Prop :=
  ∀ z₁ : Assignment N, G.eval z₁ = true →
    ∃ i, ∀ z₂ : Assignment N, G.eval z₂ = true → z₂ ≠ z₁ → (hs i).apply z₂ ≠ (hs i).apply z₁

/-- A certificate: what `AFCounter` hands the auditor (problem.tex:15-31,
combined.tex:51). `CntEst` is not a field; the auditor recomputes it from `chigh`.
`hholes` has `clow + 1` members, as `φ_holes(c_low)` has (this corrects the
`h_1 … h_{c_low}` of finalaudit.tex:23). -/
structure Cert (N : ℕ) where
  /-- `c_low`. -/
  clow : ℕ
  /-- `c_high`. -/
  chigh : ℕ
  /-- `hashassgn_stock`: `c_high` hashes into `{0,1}^{c_high}`. -/
  hstock : Fin chigh → AffHash N chigh
  /-- `hashassgn_holes`: `c_low + 1` hashes into `{0,1}^{c_low}`. -/
  hholes : Fin (clow + 1) → AffHash N clow

/-- `CntEst = 2^{c_high / log n}` (combined.tex:48), with `k = copies n`. -/
noncomputable def estimate (k chigh : ℕ) : ℝ := (2 : ℝ) ^ ((chigh : ℝ) / k)

/-- The auditor's answer. The listing (finalaudit.tex:27) has no `else` branch;
falling through is `rejected`. -/
inductive Verdict
  | verified
  | rejected
  deriving DecidableEq

/-- A quantifier-free Boolean formula over named variables `V`: the matrix of an
oracle query. -/
inductive BForm (V : Type) where
  | var : V → BForm V
  | const : Bool → BForm V
  | not : BForm V → BForm V
  | and : BForm V → BForm V → BForm V
  | or : BForm V → BForm V → BForm V
  | xor : BForm V → BForm V → BForm V

/-- The value of a `BForm` under an assignment to its variables. -/
def BForm.eval {V : Type} : BForm V → (V → Bool) → Bool
  | .var v, x => x v
  | .const b, _ => b
  | .not f, x => !f.eval x
  | .and f g, x => f.eval x && g.eval x
  | .or f g, x => f.eval x || g.eval x
  | .xor f g, x => Bool.xor (f.eval x) (g.eval x)

/-- A forall-exists QBF `∀ x ∈ {0,1}^{nU} ∃ y ∈ {0,1}^{nE}. matrix(x, y)`, the kind of
query one `Σ₂ᴾ` oracle call answers (by complementation; stock.tex:188-191). -/
structure Pi2Query where
  /-- Number of universally quantified Boolean variables. -/
  nU : ℕ
  /-- Number of existentially quantified Boolean variables. -/
  nE : ℕ
  /-- The quantifier-free matrix; universal variables are `inl`, existential `inr`. -/
  matrix : BForm (Fin nU ⊕ Fin nE)

/-- The truth of a forall-exists query. -/
def Pi2Query.holds (q : Pi2Query) : Prop :=
  ∀ x : Fin q.nU → Bool, ∃ y : Fin q.nE → Bool, q.matrix.eval (Sum.elim x y) = true

/-! ## Vocabulary of `EqualCellsCounter` (thm:intermediate)

`EqualCellsCounter(F)` (Algorithm algo:smallcells, bgp.tex:76-98) works on `F`
itself. It uses `CNF`, `sol` and `solCount` from above and none of the
`AFCounter` vocabulary (no copies, no `AffHash`, no certificate).

| paper | Lean |
|---|---|
| `ℓ = 1024 n`, `u = 16384 n` (algo:smallcells lines 1-2) | `cellsLow`, `cellsHigh` |
| `H(n, m, n)` (prelim.tex:92-118) | `CellHash`, `CellHash.apply` |
| `Cnt_⟨F, h, α⟩` (prelim.tex:123-129) | `cellCount` |
| `φ_Cells^{⟨F,ℓ,u⟩}(m)[h ← c]` (bgp.tex:20, 42-48) | `cellsWith` (prose reading; see its docstring) |
| `return (CntEst, hashassgn_cells)` (line 12) | `CellsOut` |

* **Hash family.** `H(n, m, n)` is "specified by a `k`-tuple of coefficients from
  `GF(2^max(n,m))`" (prelim.tex:112-115); here `m ≤ n`, so the field has order
  `2^n`. The field is a parameter `K` with `[Field K] [FinEnum K]` and a bit
  encoding `bits : K ≃ (Fin n → Bool)` (which forces `|K| = 2^n`), rather than
  Mathlib's `GaloisField 2 n`, whose `Fintype` is noncomputable and would put the
  program outside the computable fragment. Statements about this family hold for
  every field of order `2^n` and every encoding: stronger than the paper's one
  fixed `GF(2^n)`, and not vacuous, since `GaloisField 2 n` is such a field. The
  map from `K` to `{0,1}^m` (the paper leaves it unstated) keeps the first `m`
  bits of the encoding.
* **`φ_Cells` is the prose reading.** See `cellsWith`.
-/

/-- `ℓ = 1024 n`, the per-cell lower bound of `EqualCellsCounter`
(algo:smallcells line 2). -/
def cellsLow (n : ℕ) : ℕ := 1024 * n

/-- `u = 16384 n`, the per-cell upper bound of `EqualCellsCounter`
(algo:smallcells line 1). `u / ℓ = 16` is the approximation factor. -/
def cellsHigh (n : ℕ) : ℕ := 16384 * n

/-- A member of `H(n, m, n)`: the coefficients `c₀ … c_{n-1}` of a polynomial of
degree `< n` over a field `K` of order `2^n` (prelim.tex:112-115). The same
coefficient vector serves every output length `m ≤ n`. -/
abbrev CellHash (K : Type) (n : ℕ) : Type := Fin n → K

/-- `h(y)` for `h ∈ H(n, m, n)` with coefficients `c`: read `y` as the field
element `x = bits⁻¹ y`, evaluate `∑ⱼ cⱼ xʲ`, and keep the first `m` bits of its
encoding. Output bits `i ≥ n` (possible only when `m > n`, which
`EqualCellsCounter` never asks for) are `false`. -/
def CellHash.apply {K : Type} [Field K] {n : ℕ} (bits : K ≃ (Fin n → Bool))
    (c : CellHash K n) (m : ℕ) (y : Fin n → Bool) : Fin m → Bool :=
  fun i =>
    if hi : (i : ℕ) < n then
      bits (∑ j : Fin n, c j * (bits.symm y) ^ (j : ℕ)) ⟨i, hi⟩
    else false

/-- `Cnt_⟨F, h, α⟩` (prelim.tex:123-129): the number of solutions of `F` that the
hash with coefficients `c`, cut to `m` output bits, sends to the cell `α`. -/
def cellCount {K : Type} [Field K] {n : ℕ} (bits : K ≃ (Fin n → Bool)) (F : CNF n)
    (c : CellHash K n) (m : ℕ) (α : Fin m → Bool) : ℕ :=
  ((sol F).filter fun σ => CellHash.apply bits c m σ = α).card

/-- `φ_Cells^{⟨F,ℓ,u⟩}(m)` with its outermost `∃ h` substituted by `c`: every cell
`α ∈ {0,1}^m` holds at least `l` and at most `u` solutions of `F`.

This is the meaning the paper's prose gives (bgp.tex:20, "two of them must be
identical"; bgp.tex:42-44) and the one the proof of Proposition prop:bgp uses. It
is **not** the displayed formula: read literally, `ConstructNotMany` (bgp.tex:17,
`⋀ᵢ (F(yᵢ) ∧ h(yᵢ) = α) → ⋁_{i ≤ u} y_{u+1} = yᵢ`) fails whenever a cell holds two
solutions `a ≠ b` (take `y₁ = … = y_u = a`, `y_{u+1} = b`), so together with
`ConstructAtLeastFew` (`l ≥ 2`) it makes `φ_Cells(m)` false for every `F` and `m`.
A syntactic `Σ₃` encoding of this predicate must use the pairwise matrix
`⋁_{i<j} yᵢ = yⱼ`. -/
def cellsWith {K : Type} [Field K] {n : ℕ} (bits : K ≃ (Fin n → Bool)) (F : CNF n)
    (l u m : ℕ) (c : CellHash K n) : Prop :=
  ∀ α : Fin m → Bool, l ≤ cellCount bits F c m α ∧ cellCount bits F c m α ≤ u

/-- What `EqualCellsCounter(F)` returns (algo:smallcells line 12,
`return (CntEst, hashassgn_cells)`), together with the round `m` at which its loop
stopped, from which `CntEst = ℓ · 2^m` is computed (line 11).

`hcells` is `hashassgn_cells`: the witnessing hash on success, `none` (the
listing's initial `0`, line 3) if no round succeeded. No claim of thm:intermediate
reads it; it is kept because the auditor `EqualCellsAudit` (bgp.tex:230-242, not
formalized here) consumes it. -/
structure CellsOut (K : Type) (n : ℕ) where
  /-- The round `m ∈ [1, n]` at which the loop stopped (`n` if none succeeded). -/
  m : ℕ
  /-- `CntEst = ℓ · 2^m = 1024 n · 2^m`. -/
  cntEst : ℕ
  /-- `hashassgn_cells`. -/
  hcells : Option (CellHash K n)

/-! ## Vocabulary of `Stock` (Theorem [Stockmeyer], stock.tex:114-116)

`Stock(F)` (Algorithm algo:stock, stock.tex:84-103) is the stock loop of `AFCounter`
on its own. It is stated in the `AFCounter` vocabulary above (`copies`, `nPrime`,
`makeCopies`, `AffHash`, `stockWith`, `estimate`); the only new item is its output.

| paper | Lean |
|---|---|
| `return (v, CntEst, hashassgn_stock)` (stock.tex:100) | `StockOut` |
| `CntEst = 2^{v / log n}` (stock.tex:99) | `estimate (copies n) v` (not a field) |
-/

/-- What `Stock(F)` returns (stock.tex:100, `return (v, CntEst, hashassgn_stock)`):
the index `v` at which its loop stopped and the witnessing hashes. `CntEst` is not a
field: as for `AFCounter`, it is the real-valued read-off `estimate (copies n) v`. -/
structure StockOut (N : ℕ) where
  /-- `v`: the first `m ∈ [1, N]` whose `φ_stock` check succeeded, or the listing's
  initial `0` (stock.tex:88) if none did. -/
  v : ℕ
  /-- `hashassgn_stock`: `v` hashes into `{0,1}^v` (the empty tuple when `v = 0`). -/
  hstock : Fin v → AffHash N v

/-! ## The quantity -/

/-- **Audit complexity `r` of one query** (problem.tex:28-34): the number of Boolean
variables in its quantifier prefix (the convention of stock.tex:199-201). The
theorem reads it off the auditor's charged run: the `Σ₂ᴾ` oracle primitive of
`Model/Operations.lean` charges one `sigma2Var` per variable of the query it is
asked. Neither Mathlib nor arlib defines this notion. -/
def Pi2Query.size (q : Pi2Query) : ℕ := q.nU + q.nE

end Auditable
