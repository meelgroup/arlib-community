import Nfa.Model.Run
import Arlib.Probability.Median

/-!
# `countNFA` as mathematics: the pseudocode side

The algorithm of algorithm.tex:90-112 (`countNFA`, `countNFAcore`) with
`estimateAndSample` (algorithm.tex:64-84), `reduce` (algorithm.tex:49-56) and the
union step eq. union_sel (algorithm.tex:20-31), written over `Finset`, `ℝ` and `PMF`.
This is the object the correctness argument is carried out on.  The bridge that
proves its output law equal to `Nfa.Run.output` (the law of
`Nfa.Program.countNFA` on the drawn tape) is `Interface/ProgramModel.lean`.  Time
is not modelled here: the running-time claim is an operator on the charged program.

## Why there are two definitions

`Nfa.Program.countNFA` and `countNFA` below compute the same distribution of
answers, and neither is dead weight.

The program holds its sample sets as duplicate-free *lists* (`Program.Samples`), its
cache's row index as a sealed `Roster`, and its numbers in sealed `Scalar`
registers: ordered structures, because the algorithm's expensive operation *is* an
iteration over them, and that iteration is what the cost is charged on.  Getting
that cost right is the reason the program looks the way it does.  But a sealed
dictionary is not extensional: two sample lists holding the same words in a
different order — the same set reached by different histories — are different
terms, and so are the states that carry them.  The paper's analysis compares laws
of *sets* (`Pr[S^r(q) = T]`, `E[|hat S^r(q)|]`, conditional expectations given the
earlier sets).  `Finset` is exactly the quotient that argument needs, and `PMF` over
`Finset`-valued states is where those laws live.  Everything here is noncomputable,
like the views of `Interface/Encoding.lean`; that is not the distinction.

## Correspondence ledger

| paper (`algorithmTranscript` step) | pseudocode | program (`Nfa.Program`) |
|---|---|---|
| pre.empty (algorithm.tex:4, background.tex:32) | `nonemptySlice`, the guard in `countNFA` | `acceptsAtLength`, the guard in `countNFA` |
| countNFA.1 unroll | `layerSet` (`Q^ℓ` as a `Finset`, from `PaperNFA.layer`) | `unroll` |
| countNFA.2 line:parameters | the argument `P : Params`; `countOutput` passes `Nfa.params A n ε δ` | the argument `P`; `Run.run` passes `Nfa.params A n ε δ` |
| countNFA.3 `for 1 ≤ j ≤ μ` | `drawAll` over `List.range P.μ` in `countNFA` (independent runs) | fold over `List.range P.μ`, run `j` reading tape sites `run = j` |
| countNFA.4 line:p_q_init | `initState` (`p ≡ 1`, `S ≡ ∅`) | the `store` fold and `s0` in `coreRun` |
| countNFA.5 computeCache(0) | — (output-irrelevant, `requiredInModel = false`) | `cache` in `coreRun` |
| countNFA.6 line:S_q_init | `initState` (`S^r(q_I^0) = {λ}` for `r < α`) | `SI` in `coreRun` |
| countNFA.7 `for 1 ≤ i ≤ n` | `runLayers` over `List.range' 1 n` | fold over `List.range' 1 n` in `coreRun` |
| countNFA.8 computeCache(i) | — (cost only; see below) | the `witnessProduct` loop in `layerStep` |
| countNFA.9 `for q ∈ Q^i` | `layerList` (`≺`-order), `processLayer` | fold over `layers.getD i []` in `layerStep` |
| countNFA.10 | `estimateAndSample` | `estimateAndSample` |
| countNFA.11 line:interrupt | `storedTotal`, `interrupt` | `Scalar.le θs s.total` in `layerStep` |
| countNFA.12 updateCache(i) | — (cost only; see below) | the `Roster` rebuild in `layerStep` |
| countNFA.13 line:final_core_estimate | `coreEstimate` (`1/p(q_F^n)`) | last lines of `coreRun` |
| countNFA.14 `median(est_1..est_μ)` | `Arlib.Probability.medianOf` in `countNFA` | `Scalar.median` in `countNFA` |
| eAS.1 line:min_rho | `pred`, `rho` | `predecessors`, `ρ` in `estimateAndSample` |
| eAS.2 line:normalize | `extendSet`, `normalize` (via `reduce`) | the `coin ⟨j, q, r, some q_i, u⟩` loop |
| eAS.3 line:union | `chosen`, `unionSel`, `hatSample` | `isWitness` |
| eAS.4 line:mean | `blockMean` | `Ys` |
| eAS.5 line:median | `blockMedian` | `Scalar.median Ys` |
| eAS.6 line:take_min | `takeMin` | the `medZero` branch |
| eAS.7 `N(q) = 1/p(q)` | — (bookkeeping, `requiredInModel = false`) | omitted |
| eAS.8 line:final_reduce | `finalReduce` (via `reduce`) | the `coin ⟨j, q, r, none, u⟩` loop |
| reduce | `reduce`, one `digitCoin` per element | one `coin` per element of the set iterated |
| union.witness | `chosen` reads `σ.pick` directly | `isWitness` reads `σ.pick` after a cache lookup |

## Decisions, and where the two sides are allowed to differ

* **State of a run.**  The paper's `p(q^ℓ)` and `S^r(q^ℓ)` for every unrolled state
  `q^ℓ ∈ Q^u` are held as `CoreState.p ℓ q` and `CoreState.S ℓ q r`, for all layers
  at once, exactly as line:p_q_init initialises them.  The program keeps only the
  previous and the current layer (`prevP`/`curP`, `prevS`/`curS`); that is a
  representation choice, and the bridge relates the program's two layers to
  `p (i-1)`, `p i`.  In particular `est_j = 1/p(q_F^n)` reads `p n q_F`, which is
  still `1` if the run was interrupted before `q_F^n` was processed — the program's
  `if s.layerIdx = n then s.curP q_F else 1` is the same value.
* **The coin.**  `digitCoin p` is the law of `Operations.bernoulliDigit k p` with
  `k ∼ Run.coinIndex` (Geometric(1/2)), i.e. exactly the law the program's `coin`
  has on the tape `Model/Run.lean` draws — not `PMF.bernoulli`.  That it *is*
  Bernoulli(`p`) for `p ∈ [0, 1]` is an analysis obligation (where the invariant
  `0 < p(q) ≤ ρ(q) ≤ 1` is available), not something this file assumes; stating the
  pseudocode with a clamped `PMF.bernoulli` would have put that invariant into every
  bridge lemma.  `digit` is `bernoulliDigit` read on a real argument;
  `bernoulliDigit_eq_digit` is the cast.
* **Lazy coins.**  The pseudocode draws each `reduce` coin when it is needed; the
  program reads a tape drawn up front, one independent draw per `Site`.  These are the
  same law because no execution reads a site twice and `Run.sites` lists every site
  read (`Model/Run.lean`); that is the bridge's argument.
* **Union.**  `chosen σ q q' u` tests `σ.pick q w b = some q'` for `u = w·b` directly,
  as eq. union_sel does.  The program asks `isWitness`, which consults `σ` only when
  `w` is a row of the cache and otherwise drops the sample.  Every word the program
  queries at layer `i` is in `S^{i-1}`, which is exactly the cache's row set, so the
  two agree on every reachable state; that is a program invariant for the bridge,
  not a hypothesis of anything here.
* **`hat ρ = +∞` when the median is `0`** (algorithm.tex:125, commented in the
  source): `takeMin ρ med = ρ` when `med ≤ 0`, else `min ρ (1/med)`.  The test is
  `med ≤ 0`, the comparison the program performs (`Scalar.le med zero`); block means
  are nonnegative, so this is the paper's `med = 0`.  Never `0⁻¹`.
* **Median convention.**  `Arlib.Probability.medianOf`, the `⌊k/2⌋`-th order
  statistic, `0` on no entries; the program's `Scalar.median` takes the same entry of
  a merge-sorted list.  That the two values agree is a bridge claim.
* **Empty predecessor list.**  `rho` is `1` when `pred(q)` is empty, as the program's
  `[] => one` branch.  For `q ∈ Q^i`, `i ≥ 1`, `pred(q)` is never empty.
* **Order inside a layer.**  `≺`-order (`Finset.sort`), as the program; only the
  interrupt's timing depends on it.
* **Cache (countNFA.5, .8, .12).**  computeCache/updateCache do not change the output
  law (introduction.tex:160-163); the pseudocode decides union membership through
  `σ` and has no cache.  Their role is cost, which stays on the program side.

No step of the restatement's transcript is missing from `Model/Program.lean`, and no
`MODEL:` gap was found: every departure from the listing is one the program's own
ledger records (in-layer `≺`-order, order-statistic median, `hat ρ = +∞` branch, `0`
on an empty slice, selector `σ` for eq. union, the listing's typos corrected).
-/

set_option autoImplicit false

namespace Nfa.Pseudocode

open Nfa.Model.Operations

/-! ## Generic probability combinators -/

/-- **Independent draws, one per listed index**, collected as a function; an index
off the list reads as the default `d`.  Used for the `α` repetitions, the
predecessors of one state, the elements of a `reduce` call's output and the `μ`
core runs — every place the paper draws independently. -/
noncomputable def drawAll {ι β : Type} [DecidableEq ι] (f : ι → PMF β) (d : β) :
    List ι → PMF (ι → β)
  | [] => PMF.pure fun _ => d
  | i :: is => (f i).bind fun b => (drawAll f d is).map fun g => Function.update g i b

/-- **The coin's digit rule on a real bias**: `Operations.bernoulliDigit` read on
`ℝ`.  Heads when `1 ≤ p`, else the `(k+1)`-st binary digit of `p`. -/
noncomputable def digit (k : ℕ) (p : ℝ) : Bool :=
  if 1 ≤ p then true else decide (⌊p * 2 ^ (k + 1)⌋ % 2 = 1)

/-- **One coin of `reduce`**, with exactly the law the program's `coin` has on a
tape drawn by `Model/Run.lean`: the digit rule applied to one Geometric(1/2) index. -/
noncomputable def digitCoin (p : ℝ) : PMF Bool :=
  Run.coinIndex.map fun k => digit k p

/-- **`reduce(S, p)`** (algorithm.tex:49-56): keep each element of `S`
independently, by one `digitCoin p` per element. -/
noncomputable def reduce (S : Finset (List Bool)) (p : ℝ) : PMF (Finset (List Bool)) :=
  (drawAll (fun _ => digitCoin p) false S.toList).map fun keep => S.filter (keep · = true)

/-! ## The unrolled automaton -/

section Automaton

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- **`Q^ℓ` as a `Finset`** (countNFA.1): the states reachable from `q_I` by a word of
length exactly `ℓ`, i.e. `PaperNFA.layer`. -/
noncomputable def layerSet (A : PaperNFA Q) (ℓ : ℕ) : Finset Q := by
  classical exact Finset.univ.filter (· ∈ A.layer ℓ)

/-- **countNFA.9**: the states of `Q^ℓ` in `≺`-order, the order they are processed. -/
noncomputable def layerList (A : PaperNFA Q) (ℓ : ℕ) : List Q :=
  (layerSet A ℓ).sort (· ≤ ·)

/-- **pre.empty** (algorithm.tex:4, background.tex:32): is `q_F ∈ Q^n`, i.e. is
`ℒ_n(𝒜)` nonempty? -/
def nonemptySlice (A : PaperNFA Q) (n : ℕ) : Prop := A.qF ∈ layerSet A n

/-- **`Σ(q', q)`** (background.tex:18): the labels `b` with `(q', b, q) ∈ Δ`. -/
def labels (A : PaperNFA Q) (q' q : Q) : Finset Bool :=
  Finset.univ.filter fun b => A.delta q' b q = true

/-- **`pred(q^i)`** in the unrolled automaton (background.tex:18, 32): the states
`q'` of `Q^{i-1}` with `Σ(q', q) ≠ ∅`. -/
noncomputable def pred (A : PaperNFA Q) (i : ℕ) (q : Q) : Finset Q :=
  (layerSet A (i - 1)).filter fun q' => (labels A q' q).Nonempty

/-- `pred(q^i)` in `≺`-order: the order its draws are listed in. -/
noncomputable def predList (A : PaperNFA Q) (i : ℕ) (q : Q) : List Q :=
  (pred A i q).sort (· ≤ ·)

end Automaton

/-! ## The state of one core run -/

/-- **What one run of `countNFAcore` holds**: `p(q^ℓ)` and `S^r(q^ℓ)` for every
unrolled state, and whether line:interrupt has fired. -/
structure CoreState (Q : Type) where
  /-- `p(q^ℓ)`, the current estimate of `1/|ℒ(q^ℓ)|` (`1` until `q^ℓ` is processed). -/
  p : ℕ → Q → ℝ
  /-- `S^r(q^ℓ)`, the `r`-th sample set of `q^ℓ` (`∅` until `q^ℓ` is processed). -/
  S : ℕ → Q → ℕ → Finset (List Bool)
  /-- Whether line:interrupt has fired. -/
  stopped : Bool

section Core

variable {Q : Type} [Fintype Q] [LinearOrder Q]

/-- **countNFA.4 line:p_q_init and countNFA.6 line:S_q_init**: `p(q) = 1` and
`S^r(q) = ∅` for every `q ∈ Q^u`, then `S^r(q_I^0) = {λ}` for `r ∈ [α]`. -/
def initState (A : PaperNFA Q) (P : Params) : CoreState Q where
  p := fun _ _ => 1
  S := fun ℓ q r => if ℓ = 0 ∧ q = A.qI ∧ r < P.α then {[]} else ∅
  stopped := false

/-! ### `estimateAndSample(q)` for `q ∈ Q^i` (algorithm.tex:64-84) -/

/-- **eAS.1 line:min_rho**: `ρ(q) = min(p(q_1), …, p(q_k))` over `pred(q)`
(the listing's `min(q_1, …, q_k)` is a typo); `1` if `pred(q)` is empty, a branch
never taken for `q ∈ Q^i`, `i ≥ 1`. -/
noncomputable def rho (A : PaperNFA Q) (st : CoreState Q) (i : ℕ) (q : Q) : ℝ :=
  if h : (pred A i q).Nonempty then (pred A i q).inf' h (st.p (i - 1)) else 1

/-- **`T·L`**: every word of `T` extended on the right by every label of `L`. -/
def extendSet (T : Finset (List Bool)) (L : Finset Bool) : Finset (List Bool) :=
  (T ×ˢ L).image fun x => x.1 ++ [x.2]

/-- **eAS.2 line:normalize**: `bar S^r(q, q') = reduce(S^r(q')·Σ(q', q), ρ(q)/p(q'))`,
for `q'` a predecessor in `Q^{i-1}` (labels from `q'` to `q`; the prose's
`Σ(q, q_i)` is a typo). -/
noncomputable def normalize (A : PaperNFA Q) (st : CoreState Q) (i : ℕ) (q : Q) (ρ : ℝ)
    (r : ℕ) (q' : Q) : PMF (Finset (List Bool)) :=
  reduce (extendSet (st.S (i - 1) q' r) (labels A q' q)) (ρ / st.p (i - 1) q')

/-- **The selector's verdict on a sample** (eq. union_sel): `u = w·b` is kept from
`bar S^r(q, q')` iff `σ` picks `q'` for `(q, w, b)`. -/
def chosen {A : PaperNFA Q} (σ : Selector A) (q q' : Q) (u : List Bool) : Prop :=
  ∃ w b, u = w ++ [b] ∧ σ.pick q w b = some q'

/-- **eAS.3 line:union** (eq. union_sel; eq. union when `σ` is the `≺`-least
candidate): `hat S^r(q) = {u ∈ ⋃_{q'} bar S^r(q, q') : u ∈ bar S^r(q, σ(u, q))}`. -/
noncomputable def unionSel {A : PaperNFA Q} (σ : Selector A) (q : Q) (preds : Finset Q)
    (bar : Q → Finset (List Bool)) : Finset (List Bool) := by
  classical exact preds.biUnion fun q' => (bar q').filter (chosen σ q q')

/-- **eAS.2–eAS.3 for one repetition `r`**: draw `bar S^r(q, q')` independently for
every predecessor `q'`, then take the selector union. -/
noncomputable def hatSample (A : PaperNFA Q) (σ : Selector A) (st : CoreState Q) (i : ℕ)
    (q : Q) (ρ : ℝ) (r : ℕ) : PMF (Finset (List Bool)) :=
  (drawAll (normalize A st i q ρ r) ∅ (predList A i q)).map (unionSel σ q (pred A i q))

/-- **`hat S^r(q)` for all `r ∈ [α]`**, independent across `r`. -/
noncomputable def hatSamples (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (st : CoreState Q) (i : ℕ) (q : Q) (ρ : ℝ) : PMF (ℕ → Finset (List Bool)) :=
  drawAll (hatSample A σ st i q ρ) ∅ (List.range P.α)

/-- **eAS.4 line:mean**: `Y_{q,b} = (1/(β ρ(q))) Σ_{r<β} |hat S^{βb+r}(q)|`, for the
block `b < γ` (0-indexed; analysis.tex:100's `b ≤ α` is a typo). -/
noncomputable def blockMean (P : Params) (ρ : ℝ) (hatS : ℕ → Finset (List Bool)) (b : ℕ) :
    ℝ :=
  (∑ r ∈ Finset.range P.β, ((hatS (P.β * b + r)).card : ℝ)) / ((P.β : ℝ) * ρ)

/-- **eAS.5 line:median**: the median of `Y_{q,0}, …, Y_{q,γ-1}` (order statistic
`⌊γ/2⌋`), whose inverse is `hat ρ(q)`. -/
noncomputable def blockMedian (P : Params) (ρ : ℝ) (hatS : ℕ → Finset (List Bool)) : ℝ :=
  Arlib.Probability.medianOf fun b : Fin P.γ => blockMean P ρ hatS b

/-- **eAS.5–eAS.6 line:take_min**: `p(q) = min(ρ(q), hat ρ(q))` with
`hat ρ(q) = 1/med`, read as `+∞` when the median is `0` (algorithm.tex:125), so that
`p(q) = ρ(q)` there.  Never `0⁻¹`. -/
noncomputable def takeMin (ρ med : ℝ) : ℝ :=
  if med ≤ 0 then ρ else min ρ (1 / med)

/-- **eAS.8 line:final_reduce**: `S^r(q) = reduce(hat S^r(q), p(q)/ρ(q))`, for all
`r ∈ [α]`, independent across `r`. -/
noncomputable def finalReduce (P : Params) (hatS : ℕ → Finset (List Bool)) (ρ p : ℝ) :
    PMF (ℕ → Finset (List Bool)) :=
  drawAll (fun r => reduce (hatS r) (p / ρ)) ∅ (List.range P.α)

/-- **`estimateAndSample(q)`** (countNFA.10; algorithm.tex:64-84) for `q ∈ Q^i`:
eAS.1–eAS.8, writing `p(q^i)` and `S^r(q^i)`. -/
noncomputable def estimateAndSample (A : PaperNFA Q) (σ : Selector A) (P : Params)
    (i : ℕ) (st : CoreState Q) (q : Q) : PMF (CoreState Q) :=
  let ρ := rho A st i q
  (hatSamples A σ P st i q ρ).bind fun hatS =>
    let p := takeMin ρ (blockMedian P ρ hatS)
    (finalReduce P hatS ρ p).map fun S' =>
      { st with
        p := Function.update st.p i (Function.update (st.p i) q p)
        S := Function.update st.S i (Function.update (st.S i) q S') }

/-! ### The core loop -/

/-- **`Σ_{r ∈ [α], q ∈ Q^u} |S^r(q)|`**, the stored-sample count of line:interrupt,
over the layers `0..n` of the unrolled automaton. -/
noncomputable def storedTotal (A : PaperNFA Q) (n : ℕ) (P : Params) (st : CoreState Q) : ℕ :=
  ∑ ℓ ∈ Finset.range (n + 1), ∑ q ∈ layerSet A ℓ, ∑ r ∈ Finset.range P.α, (st.S ℓ q r).card

/-- **countNFA.11 line:interrupt**: after an `estimateAndSample` call, stop the run
once the stored samples reach `θ`. -/
noncomputable def interrupt (A : PaperNFA Q) (n : ℕ) (P : Params) (st : CoreState Q) :
    CoreState Q :=
  { st with stopped := decide (P.θ ≤ storedTotal A n P st) }

/-- **countNFA.9–11**: `estimateAndSample(q)` for the listed states of layer `i`, in
order, with the interrupt test after each; nothing more once it has fired. -/
noncomputable def processLayer (A : PaperNFA Q) (σ : Selector A) (P : Params) (n i : ℕ) :
    CoreState Q → List Q → PMF (CoreState Q)
  | st, [] => PMF.pure st
  | st, q :: qs =>
      if st.stopped then PMF.pure st else
        (estimateAndSample A σ P i st q).bind fun st' =>
          processLayer A σ P n i (interrupt A n P st') qs

/-- **One iteration `i` of countNFA.7**: the states of `Q^i` in `≺`-order
(computeCache(i) and updateCache(i) are output-irrelevant and omitted). -/
noncomputable def layerStep (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ)
    (st : CoreState Q) (i : ℕ) : PMF (CoreState Q) :=
  if st.stopped then PMF.pure st else processLayer A σ P n i st (layerList A i)

/-- **countNFA.7**: the listed layers, in order. -/
noncomputable def runLayers (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ) :
    CoreState Q → List ℕ → PMF (CoreState Q)
  | st, [] => PMF.pure st
  | st, i :: is => (layerStep A σ P n st i).bind fun st' => runLayers A σ P n st' is

/-- **The final state of one run of `countNFAcore`** (countNFA.4–12): every `p(q^ℓ)`
and `S^r(q^ℓ)` the run wrote, and whether it was interrupted.  Exposed because the
analysis is about these, not only about `est_j`. -/
noncomputable def coreLaw (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ) :
    PMF (CoreState Q) :=
  runLayers A σ P n (initState A P) (List.range' 1 n)

/-- **countNFA.13 line:final_core_estimate**: `est_j = 1/p(q_F^n)`; `p(q_F^n)` is
still `1` if the run was interrupted before processing `q_F^n`. -/
noncomputable def coreEstimate (A : PaperNFA Q) (n : ℕ) (st : CoreState Q) : ℝ :=
  1 / st.p n A.qF

/-- **One run of `countNFAcore`**: the law of `est_j`. -/
noncomputable def coreRun (A : PaperNFA Q) (σ : Selector A) (P : Params) (n : ℕ) : PMF ℝ :=
  (coreLaw A σ P n).map (coreEstimate A n)

/-- **`countNFA(𝒜, n, ε, δ)`** with parameter block `P` (algorithm.tex:90-112):
`0` on an empty slice (pre.empty), otherwise the median of `μ` independent core-run
estimates (countNFA.3, countNFA.14). -/
noncomputable def countNFA (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (P : Params) :
    PMF ℝ := by
  classical exact
    if nonemptySlice A n then
      (drawAll (fun _ => coreRun A σ P n) 0 (List.range P.μ)).map fun ests =>
        Arlib.Probability.medianOf fun j : Fin P.μ => ests j
    else PMF.pure 0

/-- **The law of the returned estimate `est`**, with the paper's parameters
`Nfa.params A n ε δ` (countNFA.2) — the pseudocode counterpart of `Nfa.Run.output`. -/
noncomputable def countOutput (A : PaperNFA Q) (σ : Selector A) (n : ℕ) (ε δ : ℝ) : PMF ℝ :=
  countNFA A σ n (params A n ε δ)

end Core

/-! ## Bridging arithmetic -/

/-- **The program's coin rule is the pseudocode's on the cast bias**: the digit rule
`Operations.bernoulliDigit` on a rational `x` is `digit` on `(x : ℝ)`. -/
theorem bernoulliDigit_eq_digit (k : ℕ) (x : ℚ) : bernoulliDigit k x = digit k (x : ℝ) := by
  have h1 : (1 ≤ (x : ℝ)) ↔ 1 ≤ x := by exact_mod_cast Iff.rfl
  have h2 : ⌊(x : ℝ) * 2 ^ (k + 1)⌋ = ⌊x * 2 ^ (k + 1)⌋ := by
    rw [← Rat.floor_cast (α := ℝ)]
    push_cast
    rfl
  unfold bernoulliDigit digit
  simp only [h1, h2]

end Nfa.Pseudocode
