import Nfa.Model.Operations
import Nfa.Meta.CostSeal
import Nfa.Meta.ModelClosure

/-!
# `countNFA`, as a charged program

The algorithm of algorithm.tex:90-112 (`countNFA`, `countNFAcore`) with
`estimateAndSample` (algorithm.tex:64-84), `reduce` (algorithm.tex:49-56), the union
step through witnesses (eq. union_sel, union_witness algorithm.tex:179-187) and the
cache maintenance (`computeCache`, `updateCache`, algorithm.tex:129-161), written
in the currency of `Nfa.Model.Operations`.  The randomness is the sealed tape
argument; its law is fixed in `Nfa.Model.Run`.

## Correspondence ledger

| paper | Lean |
|---|---|
| preprocessing "`ℒ_n(𝒜) ≠ ∅`" (algorithm.tex:4, background.tex:32) | `acceptsAtLength`, the guard in `countNFA`: returns `0` when `q_F ∉ Q^n` |
| countNFA.1 unroll | `unroll` (layers `Q^0..Q^n` by forward reachability, each in `≺`-order) |
| countNFA.2 line:parameters | the argument `P : Params`; the caller passes `Nfa.params A n ε δ` (real arithmetic is not computable) |
| countNFA.3 `for 1 ≤ j ≤ μ` | the fold over `List.range P.μ` in `countNFA`; run `j` reads only tape sites with `run = j` |
| countNFA.4 line:p_q_init | the `store` fold in `coreRun`; `p` defaults to `1`, `S` to `∅` |
| countNFA.5 computeCache(0) | `cache` holding the single row `λ` in `coreRun` |
| countNFA.6 line:S_q_init | `SI` in `coreRun` (`S^r(q_I) = {λ}`, and these `α` samples start the interrupt count) |
| countNFA.7 `for 1 ≤ i ≤ n` | the fold over `List.range' 1 n` in `coreRun` |
| countNFA.8 computeCache(i) | the `witnessProduct` loop in `layerStep`: `2·⌈|S^{i-1}|/m⌉` blocks, `m = |Q|` |
| countNFA.9 `for q ∈ Q^i` | the fold over the layer, in `≺`-order (the paper leaves the order open) |
| countNFA.10 | `estimateAndSample` |
| countNFA.11 line:interrupt | `Scalar.le θ total` after each call; `total` is `Σ_{r, q ∈ Q^u} |S^r(q)|`, never reset between layers |
| countNFA.12 updateCache(i) | the `Roster` rebuild in `layerStep`: one row per distinct word of `S^i`, `|Q^i|` entries each |
| countNFA.13 line:final_core_estimate | the last two lines of `coreRun`: `1/p(q_F^n)`, with `p(q_F^n) = 1` if the run stopped before processing it |
| countNFA.14 `median(est_1..est_μ)` | `Scalar.median` at the end of `countNFA` |
| eAS.1 line:min_rho | `ρ` in `estimateAndSample` (the listing's `min(q_1,…,q_k)` is a typo for `min p(q_i)`) |
| eAS.2 line:normalize | the `coin ⟨j, q, r, some q_i, u⟩` loop, bias `ρ(q)/p(q_i)`, over `S^r(q_i)·Σ(q_i, q)` (labels from `q_i` to `q`; the prose's `Σ(q, q_i)` is a typo) |
| eAS.3 line:union | `isWitness`: a kept `u = w·b` from `bar S^r(q, q_i)` enters `hat S^r(q)` iff `σ` picks `q_i` (the listing's `S^r(q, q_j)` means `bar S^r(q, q_j)`) |
| eAS.4 line:mean | `Ys`: `Y_{q,b} = (1/(βρ(q))) Σ_{r<β} |hat S^{βb+r}(q)|` for `b < γ` (γ blocks; analysis.tex:100's `b ≤ α` is a typo) |
| eAS.5 line:median, eAS.6 line:take_min | `p := ρ` if the median is `0` (`hat ρ = +∞`, algorithm.tex:125), else `min(ρ, 1/median)` — never `0⁻¹` |
| eAS.7 `N(q) = 1/p(q)` | omitted: bookkeeping never read except as `est_j`, which countNFA.13 computes |
| eAS.8 line:final_reduce | the `coin ⟨j, q, r, none, u⟩` loop, bias `p(q)/ρ(q)` |
| reduce | each reduce call is the fold over its set with one `coin` per element |

Representation choices, none of which changes the output law: the unrolled state
`q^ℓ` is held as `q` in the layer being processed (`curP`, `curS`) or the one before
it (`prevP`, `prevS`), since layer `i` reads only layer `i-1`; a sample set is a
duplicate-free list of words (each word of a reduce call is decided once, and the
union keeps a word from exactly the predecessor `σ` chooses); the cache stores only
its row index, and its witness entries are answered by `σ` through
`Operations.isWitness` and paid for by `witnessProduct` (see `Nfa.Model.Operations`).
Iterating a held list is free; every element it visits is charged by the body.
-/

set_option autoImplicit false

namespace Nfa.Program

open Arlib.Computation (Charged Roster)
open Nfa.Model.Operations

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- The sample sets `S^r(q)` of one state, indexed by the repetition `r ∈ [α]`. -/
abbrev Samples : Type := Array (List (List Bool))

/-- **What one core run holds between two `estimateAndSample` calls.** -/
structure CoreState (Q : Type) where
  /-- `p(q^{i-1})` for the states of the previous layer. -/
  prevP : Q → Scalar
  /-- `S^r(q^{i-1})` for the states of the previous layer. -/
  prevS : Q → Samples
  /-- `p(q^i)` for the layer being processed (`1` until `q` is processed). -/
  curP : Q → Scalar
  /-- `S^r(q^i)` for the layer being processed (`∅` until `q` is processed). -/
  curS : Q → Samples
  /-- The index `i` of the layer being processed. -/
  layerIdx : ℕ
  /-- `Σ_{r ∈ [α], q ∈ Q^u} |S^r(q)|`, over every state processed so far. -/
  total : Scalar
  /-- The words of `S^{i-1}`: the rows of `cache_{i-1}`. -/
  cache : Roster (List Bool)
  /-- Whether line:interrupt has fired. -/
  stopped : Bool

/-- **countNFA.1**: the layers `Q^0 = {q_I}, …, Q^n` of the unrolled automaton,
`Q^{ℓ+1}` being the states with a transition from `Q^ℓ`, each listed in `≺`-order.
Two `Δ` lookups per (state, state) pair per layer. -/
def unroll (A : PaperNFA Q) (n : ℕ) : Charged Op Cell (Array (List Q)) :=
  let states : List Q := (Finset.univ : Finset Q).sort (· ≤ ·)
  Charged.foldl (fun (layers : Array (List Q)) (_ : ℕ) => do
      let last := layers.back?.getD []
      let next ← Charged.foldl (fun (acc : List Q) (q : Q) => do
          let hit ← Charged.foldl (fun (hit : Bool) (q' : Q) =>
              Charged.foldl (fun (hit : Bool) (b : Bool) => do
                  let t ← transition A q' b q
                  pure (hit || t)) [false, true] hit) last false
          pure (if hit then acc ++ [q] else acc)) states []
      pure (layers.push next)) (List.range n) #[[A.qI]]

/-- **The emptiness preprocessing** (algorithm.tex:4, background.tex:32): is
`q_F ∈ Q^n`, i.e. is `ℒ_n(𝒜)` nonempty? -/
def acceptsAtLength (A : PaperNFA Q) (layers : Array (List Q)) (n : ℕ) :
    Charged Op Cell Bool :=
  Charged.foldl (fun (acc : Bool) (q : Q) => do
      let e ← sameState q A.qF
      pure (acc || e)) (layers.getD n []) false

/-- **`pred(q)` in the unrolled automaton** (background.tex:18, 32): the states
`q'` of the previous layer with `Σ(q', q) ≠ ∅`, in `≺`-order, each paired with
`Σ(q', q) = {b | (q', b, q) ∈ Δ}`. -/
def predecessors (A : PaperNFA Q) (prev : List Q) (q : Q) :
    Charged Op Cell (List (Q × List Bool)) :=
  Charged.foldl (fun (acc : List (Q × List Bool)) (q' : Q) => do
      let labels ← Charged.foldl (fun (ls : List Bool) (b : Bool) => do
          let t ← transition A q' b q
          pure (if t then ls ++ [b] else ls)) [false, true] []
      pure (if labels.isEmpty then acc else acc ++ [(q', labels)])) prev []

/-- **`estimateAndSample(q)`** (algorithm.tex:64-84) for a state `q` of layer `i`,
in core run `j`, given the previous layer `prev`. -/
def estimateAndSample (A : PaperNFA Q) (σ : Selector A) (P : Params) (tape : Tape Q)
    (j : ℕ) (prev : List Q) (one zero : Scalar) (s : CoreState Q) (q : Q) :
    Charged Op Cell (CoreState Q) := do
  let preds ← predecessors A prev q
  -- eAS.1 line:min_rho: ρ(q) = min(p(q_1), …, p(q_k)).  `pred(q)` is nonempty for
  -- every q ∈ Q^i, i ≥ 1 (a proof obligation); the empty branch is never taken.
  let ρ ← match preds with
    | [] => pure one
    | (q₁, _) :: rest =>
        Charged.foldl (fun (m : Scalar) (e : Q × List Bool) => Scalar.min m (s.prevP e.1))
          rest (s.prevP q₁)
  -- the probability ρ(q)/p(q_i) of each reduce call of line:normalize
  let normalized ← Charged.foldl
      (fun (acc : List (Q × List Bool × Scalar)) (e : Q × List Bool) => do
        let ratio ← Scalar.div ρ (s.prevP e.1)
        pure (acc ++ [(e.1, e.2, ratio)])) preds []
  -- eAS.2 line:normalize and eAS.3 line:union, for each r ∈ [α]:
  -- bar S^r(q, q_i) = reduce(S^r(q_i)·Σ(q_i, q), ρ(q)/p(q_i)), and u = w·b ∈ bar S^r(q, q_i)
  -- enters hat S^r(q) iff σ picks q_i for (q, w, b)
  let hatS ← Charged.foldl (fun (acc : Samples) (r : ℕ) => do
      let T ← Charged.foldl (fun (T : List (List Bool)) (e : Q × List Bool × Scalar) =>
          Charged.foldl (fun (T : List (List Bool)) (w : List Bool) =>
              Charged.foldl (fun (T : List (List Bool)) (b : Bool) => do
                  let u ← extend w b
                  let kept ← coin ⟨j, q, r, some e.1, u⟩ e.2.2 tape
                  if kept then do
                    let chosen ← isWitness σ s.cache q w b e.1
                    if chosen then addWord u T else pure T
                  else pure T) e.2.1 T)
            ((s.prevS e.1).getD r []) T) normalized []
      pure (acc.push T)) (List.range P.α) #[]
  -- eAS.4 line:mean: Y_{q,b} = (1/(β ρ(q))) Σ_{r<β} |hat S^{βb+r}(q)|, for b < γ
  let βs ← Scalar.lit (P.β : ℚ)
  let βρ ← Scalar.mul βs ρ
  let Ys ← Charged.foldl (fun (Ys : List Scalar) (b : ℕ) => do
      let sum ← Charged.foldl (fun (acc : Scalar) (r : ℕ) => do
          let c ← size (hatS.getD (P.β * b + r) [])
          Scalar.add acc c) (List.range P.β) zero
      let y ← Scalar.div sum βρ
      pure (Ys ++ [y])) (List.range P.γ) []
  -- eAS.5 line:median and eAS.6 line:take_min: hat ρ(q) = median⁻¹, read as +∞ when
  -- the median is 0 (algorithm.tex:125), so p(q) = ρ(q) there
  let med ← Scalar.median Ys
  let medZero ← Scalar.le med zero
  let p ← if medZero then pure ρ else do
      let hatρ ← Scalar.div one med
      Scalar.min ρ hatρ
  -- eAS.8 line:final_reduce: S^r(q) = reduce(hat S^r(q), p(q)/ρ(q))
  let ratio ← Scalar.div p ρ
  let out ← Charged.foldl (fun (acc : Samples × Scalar) (r : ℕ) => do
      let T ← Charged.foldl (fun (T : List (List Bool)) (u : List Bool) => do
          let kept ← coin ⟨j, q, r, none, u⟩ ratio tape
          if kept then addWord u T else pure T) (hatS.getD r []) []
      let c ← size T
      let tot ← Scalar.add acc.2 c
      pure (acc.1.push T, tot)) (List.range P.α) (#[], s.total)
  pure { s with curP := Function.update s.curP q p, curS := Function.update s.curS q out.1,
                total := out.2 }

/-- **One iteration `i` of countNFA.7**: computeCache(i), every state of `Q^i` with
the interrupt test after each, then updateCache(i).  Once the interrupt has fired
the remaining iterations do nothing. -/
def layerStep (A : PaperNFA Q) (σ : Selector A) (P : Params) (tape : Tape Q) (j : ℕ)
    (layers : Array (List Q)) (one zero θs : Scalar) (s : CoreState Q) (i : ℕ) :
    Charged Op Cell (CoreState Q) :=
  if s.stopped then pure s else do
    -- countNFA.8 computeCache(i): cache'_i = [cache_{i-1}·T⁰ ; cache_{i-1}·T¹], as
    -- ⌈|S^{i-1}|/m⌉ products of m × m blocks for each b ∈ {0, 1}
    let rows ← Roster.size s.cache
    let blocks ← ceilDiv rows (Fintype.card Q)
    let _ ← Charged.foldl (fun (_ : Unit) (_ : Bool) =>
        Charged.foldl (fun (_ : Unit) (_ : ℕ) => witnessProduct) (List.range blocks) ())
      [false, true] ()
    let prev := layers.getD (i - 1) []
    let cur := layers.getD i []
    let s : CoreState Q :=
      { s with prevP := s.curP, prevS := s.curS, curP := fun _ => one, curS := fun _ => #[],
               layerIdx := i }
    -- countNFA.9-11: estimateAndSample(q) for q ∈ Q^i, then line:interrupt
    let s ← Charged.foldl (fun (s : CoreState Q) (q : Q) =>
        if s.stopped then pure s else do
          let s ← estimateAndSample A σ P tape j prev one zero s q
          let over ← Scalar.le θs s.total
          pure { s with stopped := over }) cur s
    -- countNFA.12 updateCache(i): one row, of |Q^i| entries, per distinct word of S^i
    if s.stopped then pure s else do
      let cache ← Charged.foldl (fun (c : Roster (List Bool)) (q : Q) =>
          Charged.foldl (fun (c : Roster (List Bool)) (T : List (List Bool)) =>
              Charged.foldl (fun (c : Roster (List Bool)) (u : List Bool) => do
                  let present ← Roster.mem u c
                  if present then pure c else do
                    let _ ← Charged.foldl (fun (_ : Unit) (_ : Q) => cacheEntry) cur ()
                    Roster.insert u c) T c)
            (s.curS q).toList c) cur Roster.empty
      pure { s with cache := cache }

/-- **`countNFAcore`, run `j`** (algorithm.tex:94-105): one pass over the layers,
returning `est_j = 1/p(q_F)`. -/
def coreRun (A : PaperNFA Q) (σ : Selector A) (P : Params) (tape : Tape Q) (n : ℕ)
    (layers : Array (List Q)) (j : ℕ) : Charged Op Cell Scalar := do
  let one ← Scalar.lit 1
  let zero ← Scalar.lit 0
  let θs ← Scalar.lit (P.θ : ℚ)
  -- countNFA.4 line:p_q_init: p(q) = 1 and S^r(q) = ∅ for q ∈ Q^u and r ∈ [α]
  let _ ← Charged.foldl (fun (_ : Unit) (layer : List Q) =>
      Charged.foldl (fun (_ : Unit) (_ : Q) =>
          Charged.foldl (fun (_ : Unit) (_ : ℕ) => store) (List.range P.α) ()) layer ())
    layers.toList ()
  -- countNFA.5 computeCache(0): cache_0 has the single row λ
  let cache ← Roster.insert ([] : List Bool) Roster.empty
  -- countNFA.6 line:S_q_init: S^r(q_I) = {λ} for r ∈ [α]; these α samples are stored
  let SI ← Charged.foldl (fun (acc : Samples) (_ : ℕ) => do
      let T ← addWord [] []
      pure (acc.push T)) (List.range P.α) #[]
  let total ← Scalar.lit (P.α : ℚ)
  let s0 : CoreState Q :=
    { prevP := fun _ => one, prevS := fun _ => #[], curP := fun _ => one,
      curS := Function.update (fun _ => #[]) A.qI SI, layerIdx := 0, total := total,
      cache := cache, stopped := false }
  -- countNFA.7: for 1 ≤ i ≤ n
  let s ← Charged.foldl (layerStep A σ P tape j layers one zero θs) (List.range' 1 n) s0
  -- countNFA.13 line:final_core_estimate: est_j = 1/p(q_F^n); p(q_F^n) is still 1
  -- if the run was interrupted before layer n processed q_F
  let pF := if s.layerIdx = n then s.curP A.qF else one
  Scalar.div one pF

/-- **`countNFA(𝒜, n, ε, δ)`** (algorithm.tex:90-112), with the parameter block `P`
(the caller supplies `Nfa.params A n ε δ`), selector `σ` and coin tape `tape`.
Returns `0` on an empty slice, and otherwise the median of `μ` core-run estimates. -/
def countNFA (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (P : Params) (tape : Tape Q) :
    Charged Op Cell Scalar := do
  -- countNFA.1 and the emptiness preprocessing
  let layers ← unroll A n
  let nonempty ← acceptsAtLength A layers n
  if nonempty then do
    -- countNFA.3: μ independent core runs
    let ests ← Charged.foldl (fun (ests : List Scalar) (j : ℕ) => do
        let e ← coreRun A σ P tape n layers j
        pure (ests ++ [e])) (List.range P.μ) []
    -- countNFA.14: return median(est_1, …, est_μ)
    Scalar.median ests
  else Scalar.lit 0

end Nfa.Program

#programSeal Nfa.Program
#executableModule Nfa.Model.Program
#surplusIn Nfa.Model.Program from Nfa.Program.countNFA
