import Arlib.Computation.Charged
import Arlib.Computation.Std
import Mathlib.Data.FinEnum
import Auditable.Model.Prelude

/-!
# What one charged step of `AFCounter` and of its auditor is

The paper works in the oracle model (prelim.tex:27-37): polynomial-time work is
free, and what is counted is oracle calls and, for the audit, the number of
Boolean variables in the quantifier prefix of each query (problem.tex:22-34). Arlib
has no QBF oracle, so this file declares a project-local currency (outcome 2 of
the brief).

## The primitives

* `Op.holesQuery` — one call to `3QBFCheck(φ_holes^{F'}(m))` (combined.tex:32), an
  exact `Σ₃ᴾ` decider that also returns the outermost witness, the `m + 1` hashes.
  Wrapper: `holesOracle`.
* `Op.stockQuery` — one call to `2QBFCheck(φ_stock^{F'}(m))` (combined.tex:41), an
  exact `Σ₂ᴾ` decider returning the `m` hashes. Wrapper: `stockOracle`.
* `Op.sigma2Query` — one call to the `Σ₂ᴾ` oracle on a syntactic forall-exists query
  (`Pi2Query`), the auditor's one merged call (finalaudit.tex:107, 136).
* `Op.sigma2Var` — one Boolean variable in the quantifier prefix of such a query.
  The wrapper `sigma2Oracle q` charges `q.size` of these, so the audit complexity
  `r` of the query the auditor actually sends is read off the auditor's tally
  rather than off a second description of the query.
* `Op.compare` — one comparison of two naturals (the gap test
  `c_high − c_low ≤ 7`, finalaudit.tex:27). Wrapper: `natLe`.

## Idealisation, stated

The oracles are exact: each wrapper's value is computed here by exhaustive
search over the finite hash family (`allHashTuples`) or by deciding the query
outright. That is the paper's oracle model (exact answers plus witnesses for the
outermost existential block), not a claim about how such oracles are built. No
`Prior` field is needed for them: their semantics is their definition.

There is no rate function. The theorem reads individual coordinates of the cost
vector (how many `sigma2Query`, how many `sigma2Var`), because summing oracle calls
with query variables under one rate would mean nothing.

`makeCopies` and the construction of the audit query's matrix are uncharged
polynomial-time work, as in the paper's model.
-/

set_option autoImplicit false

namespace Auditable.Model

namespace Operations

open Auditable
open Arlib.Computation (Charged)

/-- The paper's cost currency: oracle calls, query variables, comparisons. -/
inductive Op where
  /-- One `3QBFCheck` call on `φ_holes^{F'}(m)` (a `Σ₃ᴾ` query with witness). -/
  | holesQuery
  /-- One `2QBFCheck` call on `φ_stock^{F'}(m)` (a `Σ₂ᴾ` query with witness). -/
  | stockQuery
  /-- One call to the `Σ₂ᴾ` oracle on a forall-exists query. -/
  | sigma2Query
  /-- One quantified Boolean variable of a query sent to the `Σ₂ᴾ` oracle. -/
  | sigma2Var
  /-- One comparison of two naturals. -/
  | compare
  deriving DecidableEq

/-- One storage kind; the theorem bounds no space. -/
abbrev Cell : Type := Arlib.Computation.Cell

/-- Every function `α → β` whose values are drawn from `vals`, as a list. -/
def enumFun {α β : Type} [FinEnum α] (vals : List β) : List (α → β) :=
  (List.pi (FinEnum.toList α) fun _ => vals).map fun f a => f a (FinEnum.mem_toList a)

/-- Every member of the hash family `AffHash N m`, as a list. -/
def allHashes (N m : ℕ) : List (AffHash N m) :=
  (enumFun (α := Fin m) (enumFun (α := Fin N) [false, true])).flatMap fun A =>
    (enumFun (α := Fin m) [false, true]).map fun b => ⟨A, b⟩

/-- Every `c`-tuple of members of `AffHash N m`: the oracles' witness space. -/
def allHashTuples (c N m : ℕ) : List (Fin c → AffHash N m) :=
  enumFun (allHashes N m)

instance {N : ℕ} (G : CNF N) (m : ℕ) (hs : Fin (m + 1) → AffHash N m) :
    Decidable (holesWith G m hs) :=
  inferInstanceAs (Decidable (∀ α : Fin m → Bool, ∃ z : Assignment N,
    G.eval z = true ∧ ∃ i, (hs i).apply z = α))

instance {N : ℕ} (G : CNF N) (m : ℕ) (hs : Fin m → AffHash N m) :
    Decidable (stockWith G m hs) :=
  inferInstanceAs (Decidable (∀ z₁ : Assignment N, G.eval z₁ = true →
    ∃ i, ∀ z₂ : Assignment N, G.eval z₂ = true → z₂ ≠ z₁ →
      (hs i).apply z₂ ≠ (hs i).apply z₁))

instance (q : Pi2Query) : Decidable q.holds :=
  inferInstanceAs (Decidable (∀ x : Fin q.nU → Bool, ∃ y : Fin q.nE → Bool,
    q.matrix.eval (Sum.elim x y) = true))

/-- `(assign, ret) ← 3QBFCheck(φ_holes^G(m))` (combined.tex:32): one `holesQuery`.
Returns `some hs` with `holesWith G m hs` if a witness exists, else `none`. -/
def holesOracle {N : ℕ} (G : CNF N) (m : ℕ) :
    Charged Op Cell (Option (Fin (m + 1) → AffHash N m)) :=
  Charged.op Op.holesQuery
    ((allHashTuples (m + 1) N m).find? fun hs => decide (holesWith G m hs))

/-- `(assign, ret) ← 2QBFCheck(φ_stock^G(m))` (combined.tex:41): one `stockQuery`.
Returns `some hs` with `stockWith G m hs` if a witness exists, else `none`. -/
def stockOracle {N : ℕ} (G : CNF N) (m : ℕ) :
    Charged Op Cell (Option (Fin m → AffHash N m)) :=
  Charged.op Op.stockQuery
    ((allHashTuples m N m).find? fun hs => decide (stockWith G m hs))

/-- One `Σ₂ᴾ` oracle call on the forall-exists query `q`: charges one
`sigma2Query` and `q.size` units of `sigma2Var`, and answers whether `q` holds. -/
def sigma2Oracle (q : Pi2Query) : Charged Op Cell Bool := do
  let _ ← Charged.opMany Op.sigma2Var q.size ()
  Charged.op Op.sigma2Query (decide q.holds)

/-- One comparison `a ≤ b` of naturals. -/
def natLe (a b : ℕ) : Charged Op Cell Bool :=
  Charged.op Op.compare (decide (a ≤ b))

/-! ## The currency of `EqualCellsCounter` (thm:intermediate)

`EqualCellsCounter` (algo:smallcells, bgp.tex:76-98) asks one kind of question,
`3QBFCheck(φ_Cells^{⟨F,ℓ,u⟩}(m))` (bgp.tex:84), and the theorem counts those calls
(bgp.tex:103, 115). That primitive is not a constructor of `Op`: `Op` is left as the
`AFCounter`/auditor developments elaborated against it, and `EqualCellsCounter` gets
its own one-primitive currency `CellsOp` beside it. In this currency "no other
oracle call" holds by the type. -/

/-- The cost currency of `EqualCellsCounter`: its `Σ₃ᴾ` oracle calls. -/
inductive CellsOp where
  /-- One `3QBFCheck` call on `φ_Cells^{⟨F,ℓ,u⟩}(m)` (a `Σ₃ᴾ` query with witness). -/
  | cellsQuery
  deriving DecidableEq

instance {K : Type} [Field K] {n : ℕ} (bits : K ≃ (Fin n → Bool)) (F : CNF n)
    (l u m : ℕ) (c : CellHash K n) : Decidable (cellsWith bits F l u m c) :=
  inferInstanceAs (Decidable (∀ α : Fin m → Bool,
    l ≤ cellCount bits F c m α ∧ cellCount bits F c m α ≤ u))

/-- `(ret, assign) ← 3QBFCheck(φ_Cells^{⟨F,ℓ,u⟩}(m))` (bgp.tex:84): one
`cellsQuery`. Returns `some c` with `cellsWith bits F l u m c` if a hash in
`H(n, m, n)` witnesses the outermost `∃ h`, else `none`. Exact, by exhaustive search
over the coefficient vectors `Fin n → K`. -/
def cellsOracle {K : Type} [Field K] [FinEnum K] {n : ℕ} (bits : K ≃ (Fin n → Bool))
    (F : CNF n) (l u m : ℕ) : Charged CellsOp Cell (Option (CellHash K n)) :=
  Charged.op CellsOp.cellsQuery
    ((enumFun (α := Fin n) (FinEnum.toList K)).find? fun c =>
      decide (cellsWith bits F l u m c))

end Operations

end Auditable.Model
