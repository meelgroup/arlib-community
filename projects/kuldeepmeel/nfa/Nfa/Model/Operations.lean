import Arlib.Computation.Std
import Mathlib.Data.Rat.Floor
import Nfa.Model.Prelude

/-!
# The currency `countNFA` is charged in

The paper's running time (introduction.tex:90; analysis.tex:40-55, 67-68) is a
real-RAM count with one priced matrix primitive: one `m × m` Boolean matrix product
with witnesses costs `MM(m)`, and every reduce coin, every set insertion or lookup
and every arithmetic operation on the algorithm's numbers costs `O(1)`.  arlib's
standard currency has no real-bias coin and no witness product, so this file
declares a project-local currency (outcome 2 of the brief).

What is trusted here, and nothing else:

* **`coin`** — one Bernoulli(`p`) draw with a rational bias computed by the program
  (eAS.2 line:normalize, eAS.8 line:final_reduce, via `reduce`, algorithm.tex:49-56).
  It is the paper's idealised real-RAM coin, priced one unit.  It is realised exactly
  on a sealed tape of i.i.d. Geometric(1/2) indices (see `bernoulliDigit` and
  `Nfa.Model.Run`); that `coin` has law Bernoulli(`p`) for `p ∈ [0, 1]` is a proof
  obligation for `Analysis/`, not an assumption.  The coin does not take a proof
  that `p ∈ [0, 1]`: the program computes `p` inside a sealed register it cannot
  inspect, so the paper's invariant `0 < p(q) ≤ ρ(q) ≤ 1` is proved about the run
  in `Analysis/`.  No clamping is applied; outside `[0, 1]` the digit rule simply
  is what it is, and the analysis must show that branch is never reached.
* **`witnessProduct`** — one `m × m` block of `computeCache` (algorithm.tex:129-140,
  eq. cache_matrix_product), priced `MM(m)` by `rate`, with `m = |Q|`: every block
  is charged as if padded to `|Q| × |Q|`, so no monotonicity of `MM` is needed.
  Its result is not materialised; the witnesses it would produce are read back by
  `isWitness`, which answers with the selector `σ` — the modelling of the cited
  witness routine ("its answer is `σ(u, q)`, and producing it costs `MM` per
  block").  Sub-cubic `MM` (Czumaj–Kowaluk–Lingas, Alon–Naor) is cited, not proved.
* **`Scalar.median`** — the order-statistic median of a list, charged one `select`
  per element: linear-time selection (Blum–Floyd–Pratt–Rivest–Tarjan).  Linear
  rather than `k log k` matters: the final median is over `μ = ⌈8 ln(1/δ)⌉` values,
  and an `O(μ log μ)` median would not fit the paper's `O(… log(1/δ))` bound.
  The value returned is the `⌊k/2⌋`-th smallest entry (0-indexed), the convention of
  arlib's `Arlib.Probability.medianOf`; the paper does not fix one for even `k`.

Everything else is a unit-priced elementary step: `arith` (one operation on the
algorithm's rational numbers, including comparison), `transition` (one lookup in
`Δ`), `stateCmp` (one comparison of two states), `wordOp` (extend a sample `w ↦ w·b`,
add a sample to a set, or read a set's size), `store` (initialise one cell of
line:p_q_init), `witnessRead` (read one cached witness entry, union_witness
algorithm.tex:179-187), `cacheEntry` (copy one cache entry, updateCache), and
arlib's dictionary operations on the cache's row index.

The program's numbers are rationals in a sealed register `Scalar`: every value the
paper computes (`p(q)`, `ρ(q)`, `Y_{q,b}`, medians, ratios, `1/p(q_F)`) is a
rational function of counts and of earlier such values, so nothing is lost, and the
analysis reads them as reals through `Scalar.get`.
-/

set_option autoImplicit false

namespace Nfa.Model

namespace Operations

open Arlib.Computation

/-! ## The currency -/

/-- **The operations one run of `countNFA` can perform.** -/
inductive Op
  /-- One arithmetic operation or comparison on the algorithm's rational numbers. -/
  | arith
  /-- One Bernoulli(`p`) coin of `reduce`. -/
  | coin
  /-- One lookup of the transition relation: is `(q', b, q) ∈ Δ`? -/
  | transition
  /-- One comparison of two states. -/
  | stateCmp
  /-- One elementary operation on a sample word or a sample set: extend `w ↦ w·b`,
  add a word to a set, or read a set's size. -/
  | wordOp
  /-- Initialise one cell (`p(q) = 1`, `S^r(q) = ∅`, line:p_q_init). -/
  | store
  /-- One element's share of a linear-time median selection. -/
  | select
  /-- One `m × m` Boolean matrix product with witnesses (`computeCache`). -/
  | witnessProduct
  /-- One read of a cached witness entry `ω_b(w, q)` (`union_witness`). -/
  | witnessRead
  /-- One cache entry copied by `updateCache`. -/
  | cacheEntry
  /-- arlib's dictionary operations, on the set of words that index the cache rows.
  `erase` and `cardEq` are never performed; they are named because `RosterOps`
  requires distinct names for every dictionary operation. -/
  | rosterErase | rosterInsert | rosterSize | rosterCardEq | rosterMem
  deriving DecidableEq, Repr

namespace Op

/-- Every operation, as a list. -/
def all : List Op :=
  [.arith, .coin, .transition, .stateCmp, .wordOp, .store, .select, .witnessProduct,
   .witnessRead, .cacheEntry, .rosterErase, .rosterInsert, .rosterSize, .rosterCardEq,
   .rosterMem]

instance : Fintype Op := Fintype.ofList all (by intro o; cases o <;> simp [all])

end Op

/-- The dictionary operations, under their own names.  A name, never a price. -/
instance instRosterOps : RosterOps Op where
  charge
    | RosterOp.erase => Op.rosterErase
    | RosterOp.insert => Op.rosterInsert
    | RosterOp.size => Op.rosterSize
    | RosterOp.cardEq => Op.rosterCardEq
    | RosterOp.mem => Op.rosterMem
  charge_injective := by decide

/-- The storage currency: arlib's single `Cell` kind.  No space claim is made. -/
abbrev Cell : Type := Arlib.Computation.Cell

/-- The price of one operation before the `max 1` floor of `rate`: the witness
product costs `MM m`, everything else costs one. -/
def price (MM : ℕ → ℕ) (m : ℕ) : Op → ℕ
  | .witnessProduct => MM m
  | _ => 1

/-- **The rate the running-time claim is read in**, for a witness-product cost `MM`
and state count `m = |Q|`.  The `max 1` is the `Rate` floor (every operation costs
at least one); under the theorem's hypothesis `m² ≤ MM m` with `m ≥ 1` it is
inert. -/
def rate (MM : ℕ → ℕ) (m : ℕ) : Rate Op where
  cost o := max 1 (price MM m o)
  one_le _ := le_max_left 1 _

/-! ## Sealed numbers -/

/-- **A sealed rational register.**  The value is private and its view `get` is
noncomputable, so the program can only combine, compare and flip coins against it
through the charged operations below. -/
structure Scalar where
  private mk ::
  private val : ℚ

namespace Scalar

/-- The number held.  **Specification-only.** -/
noncomputable def get (x : Scalar) : ℚ := x.val

/-- A constant, at one `arith`. -/
def lit (a : ℚ) : Charged Op Cell Scalar := Charged.op .arith ⟨a⟩

/-- Addition, at one `arith`. -/
protected def add (x y : Scalar) : Charged Op Cell Scalar := Charged.op .arith ⟨x.val + y.val⟩

/-- Multiplication, at one `arith`. -/
protected def mul (x y : Scalar) : Charged Op Cell Scalar := Charged.op .arith ⟨x.val * y.val⟩

/-- Division, at one `arith`. -/
protected def div (x y : Scalar) : Charged Op Cell Scalar := Charged.op .arith ⟨x.val / y.val⟩

/-- The smaller of two numbers, at one `arith`. -/
protected def min (x y : Scalar) : Charged Op Cell Scalar :=
  Charged.op .arith ⟨Min.min x.val y.val⟩

/-- Comparison `x ≤ y`, at one `arith`.  The only way a number reaches control flow. -/
protected def le (x y : Scalar) : Charged Op Cell Bool := Charged.op .arith (decide (x.val ≤ y.val))

/-- **The median of a list**: its `⌊k/2⌋`-th smallest entry (0-indexed), `0` for
the empty list, at one `select` per entry (linear-time selection). -/
def median (xs : List Scalar) : Charged Op Cell Scalar := do
  let _ ← Charged.foldl (fun (_ : Unit) (_ : Scalar) => Charged.op Op.select ()) xs ()
  pure ⟨((xs.map Scalar.val).mergeSort (fun a b => decide (a ≤ b))).getD (xs.length / 2) 0⟩

end Scalar

/-! ## The randomness: a sealed tape of coin indices -/

/-- **The name of one coin of the algorithm.**  Every `reduce` coin of a run is
determined by the core run `run` (`j ∈ [μ]`), the state `state` being processed,
the repetition `rep` (`r ∈ [α]`), the reduce call it belongs to (`source = some q'`:
line:normalize for predecessor `q'`; `source = none`: line:final_reduce) and the
word `word` it decides on.  The layer is `|word|`.  No two coins of an execution
share a site, so independent draws per site are independent coins. -/
structure Site (Q : Type) where
  /-- The core run `j`. -/
  run : ℕ
  /-- The state `q` whose `estimateAndSample` call flips the coin. -/
  state : Q
  /-- The repetition `r`. -/
  rep : ℕ
  /-- `some q'` for the coin of `bar S^r(q, q')`, `none` for the coin of `S^r(q)`. -/
  source : Option Q
  /-- The sample word the coin keeps or discards. -/
  word : List Bool
  deriving DecidableEq

/-- **A sealed tape**: one natural number per coin site, drawn i.i.d. Geometric(1/2)
by `Nfa.Model.Run`.  The program cannot read it except through `coin`. -/
structure Tape (Q : Type) where
  private mk ::
  private draw : Site Q → ℕ

namespace Tape

variable {Q : Type}

/-- The tape holding given draws.  **The boundary**, noncomputable so that no
program can build the tape it wants.  Every tape the run uses is `ofFun f` for a
drawn `f`, so statements about coins are statements about `f`. -/
noncomputable def ofFun (f : Site Q → ℕ) : Tape Q := ⟨f⟩

end Tape

/-- **A Bernoulli outcome from a geometric index.**  With `k` distributed as
`P(k) = 2^{-(k+1)}`, the outcome "the `(k+1)`-st binary digit of `p` is `1`" has
probability `Σ_k 2^{-(k+1)} d_{k+1}(p) = p` for `p ∈ [0, 1)`, where `d_j(p)` is the
`j`-th digit of the terminating expansion; `p ≥ 1` is always heads.  This is the
textbook lazy comparison of `p` with a uniform real. -/
def bernoulliDigit (k : ℕ) (p : ℚ) : Bool :=
  if 1 ≤ p then true else decide (⌊p * 2 ^ (k + 1)⌋ % 2 = 1)

/-- **One Bernoulli(`p`) coin** of `reduce`, at one `coin`: the tape's draw at
`site`, read against the bias held in `p`. -/
def coin {Q : Type} (site : Site Q) (p : Scalar) (t : Tape Q) : Charged Op Cell Bool :=
  Charged.op .coin (bernoulliDigit (t.draw site) p.val)

/-! ## The automaton, samples and cache -/

/-- One lookup of `Δ`: whether `(q', b, q)` is a transition, at one `transition`. -/
def transition {Q : Type} (A : Nfa.PaperNFA Q) (q' : Q) (b : Bool) (q : Q) :
    Charged Op Cell Bool :=
  Charged.op .transition (A.delta q' b q)

/-- One comparison of two states, at one `stateCmp`. -/
def sameState {Q : Type} [DecidableEq Q] (q q' : Q) : Charged Op Cell Bool :=
  Charged.op .stateCmp (decide (q = q'))

/-- Extend a sample on the right, `w ↦ w·b`, at one `wordOp`. -/
def extend (w : List Bool) (b : Bool) : Charged Op Cell (List Bool) :=
  Charged.op .wordOp (w ++ [b])

/-- Add a word to a sample set, at one `wordOp`.  Callers only add words not
already present (each word of a reduce call is decided once). -/
def addWord (u : List Bool) (T : List (List Bool)) : Charged Op Cell (List (List Bool)) :=
  Charged.op .wordOp (u :: T)

/-- The size of a sample set, as a number, at one `wordOp`. -/
def size (T : List (List Bool)) : Charged Op Cell Scalar :=
  Charged.op .wordOp ⟨(T.length : ℚ)⟩

/-- Initialise one cell of line:p_q_init, at one `store`. -/
def store : Charged Op Cell Unit := Charged.op .store ()

/-- `⌈a / b⌉` on two counts the program holds, at one `arith`. -/
def ceilDiv (a b : ℕ) : Charged Op Cell ℕ := Charged.op .arith ((a + b - 1) / b)

/-- **One `m × m` Boolean matrix product with witnesses**, at one `witnessProduct`
(priced `MM m` by `rate`).  Cost only: the witnesses are read by `isWitness`. -/
def witnessProduct : Charged Op Cell Unit := Charged.op .witnessProduct ()

/-- Copy one entry into the cache (`updateCache`), at one `cacheEntry`. -/
def cacheEntry : Charged Op Cell Unit := Charged.op .cacheEntry ()

/-- **Read the witness `ω_b(w, q)` and test whether it is `q'`** (union_witness,
algorithm.tex:179-187).  The cache only holds rows for the words in `cache`; the
row of `w` is looked up first (one dictionary `mem`), and only a cached row is read
(one `witnessRead`).  An uncached word has no witness and the sample is dropped —
the analysis shows every queried word is cached. -/
def isWitness {Q : Type} [DecidableEq Q] {A : Nfa.PaperNFA Q} (σ : Nfa.Selector A)
    (cache : Roster (List Bool)) (q : Q) (w : List Bool) (b : Bool) (q' : Q) :
    Charged Op Cell Bool := do
  let cached ← Roster.mem w cache
  if cached then Charged.op .witnessRead (decide (σ.pick q w b = some q'))
  else pure false

end Operations

end Nfa.Model
