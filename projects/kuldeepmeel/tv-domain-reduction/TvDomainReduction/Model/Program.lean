import TvDomainReduction.Model.Prelude
import TvDomainReduction.Model.Operations
import TvDomainReduction.Meta.CostSeal
import TvDomainReduction.Meta.ModelClosure

/-!
# The bottom-up coreset propagation, transcribed and charged

§4.2 of the paper (main.tex:885–896) as a `Charged` program in the arithmetic
currency of `Model/Operations.lean`.  The theorem's three claims are three
operators applied to *this* term: `Model/Prelude.Dtilde` of its value, the
retained sizes inside its value, and `Charged.steps` of its tally.

There is **no numbered algorithm listing for the circuit case**.  Algorithm 1
(main.tex:763–784) is the mixture-of-products case.  The circuit algorithm is
three paragraphs of prose — "Leaf Gates", "Sum Gates", "Product Gates",
main.tex:888–896 — plus the parameter paragraph at main.tex:886 and the estimator
at main.tex:881–884.  So this file is a transcription of prose, and the
correspondence below is the whole of the claim that it is the paper's algorithm.

## Correspondence ledger

| paper step | Lean |
| --- | --- |
| **P0** parameters `q`, `W`, `L`, `δ = ε/(3L)`, `η' = η/L`, `m` (main.tex:886) | `Model.Prelude`: `leafDomMax`, `pairWidth`, `CircuitPair.steps`, `perStepTol`, `perStepFail`, `SparsifyPrior.size` |
| **P1** leaf: keep the exact set `{(a,1,Φ(a)) : a ∈ Ω_i}` (main.tex:888) | `build`, leaf branch: `Reduction.leaf`, charged `reads ((gP+gQ)·m)` for both circuits' lookup tables |
| **P2** sum layer: a fixed linear map, no error, no domain growth (main.tex:890) | *fused* into the node's `blockTensor cP cQ`; see the departure below |
| **P3** product region: `U_S = C_{S_h} × C_{S_ℓ}` with `μ_ij = λ_i ρ_j`, evaluate, `Sparsify(·,m,η')` (main.tex:896) | `build`, node branch: `WPS.tensor (blockTensor cP cQ)`, then `prior.out` |
| **P4** output `D̃ = ½ ∑_j μ_j |⟨a_TV,Φ_root(z_j)⟩|` (main.tex:883) | `run`: the root evaluation is charged here and its *value* is `Model.Prelude.Dtilde` of the returned `Reduction` |
| **S0** `Sparsify` / `thm:lewis_weights`, cited not proved (main.tex:745, 761) | the `prior : SparsifyPrior δ η'` argument; `prior.out` is called, never implemented |

### The recursive invariant the analysis runs on

At a product region `S_g = S_h ⊔ S_ℓ` the paper's `ℓ(S_g) = ℓ(S_h) + ℓ(S_ℓ) + 1`
(main.tex:924) is `Region.steps_node`, and arlib's `Reduction.embeds_exact` —
which **is** Lemma `lem:pc_invariant` and is already proved — consumes it.  It is
cited, never re-derived.

At every node of this recursion the retained **index type is static**: a leaf
keeps `Fin m` rows, and a product region keeps exactly
`Fin (prior.size (card (Coord gP gQ)))` rows, zero-padded.  Only the weights and
the features depend on the draw.  That is what lets `Model/Run.lean` build the
run's law as an ordinary sequential product instead of a dependent product over
random sizes.

## Departures from the brief's program grammar, and why

* **The recursion is structural on the v-tree, not a `Charged.foldl`.**  The
  brief's grammar admits bounded iteration only.  The object produced here is
  `Arlib.Approximation.Reduction S`, which is *indexed by the region tree*, so a
  fold's accumulator cannot be uniformly typed and a post-order linearisation
  would need dependent types over the visiting order.  The recursion matches
  simultaneously on both circuits, exactly as arlib's `pairRegion` does; it is
  structural, so it terminates, and the tally is still the elaborator's — every
  `bind` adds.  Reported as a deliberate departure.

* **The randomness is addressed by v-tree path, not consumed from a stream.**
  `Tape prior = List Bool → prior.Draw`: the region at path `p` reads `t p`, and
  the children read `t ∘ (false :: ·)` and `t ∘ (true :: ·)`.  No counter, no
  state threading, and the addressing is manifestly injective, which is what
  `Model/Run.lean` needs in order to give the `L` draws a joint law.

* **`D̃` itself is not a value this file produces.**  `(1/2) * …` is
  `noncomputable` in Lean (real division is), and `#executableModule` rejects
  `noncomputable` in this module — correctly, since that is the one route past
  the compiler's half of the cost seal.  So `run` charges every arithmetic
  operation of the root evaluation (`main.tex:883`) and returns the `Reduction`;
  `Model.Prelude.Dtilde` reads the number off it.  Nothing is hidden: the
  returned object determines `D̃`, and the operations that produce it are paid
  for here.  *Lean-specific departure.*

* **Charges are the model's accounting, not a by-product of evaluating reals.**
  `Charged` seals *container* reads; `ℝ` is a shallow embedding, so no amount of
  sealing makes `WPS.tensor`'s feature map charge itself.  Every charge below
  therefore names the implementation it prices, line by line, and the running
  time is a claim about that implementation.  This is stated here rather than
  discovered later.

* **The time bound this accounting yields is weaker than the paper's on one
  term, and that is a consequence of the fused node.**  main.tex:894 applies the
  same-scope linear map `L_S` **to the surviving rows only**, which is what makes
  the circuit-traversal cost `O(M|C|)` and the paper's total
  `Õ((q+M)|C| + L[W(q+M)² + W^ω])`.  arlib's `Region.node` fuses product-then-sum
  into a single bilinear tensor, so the features this program forms on *every*
  candidate row are already the post-sum ones: the per-region traversal cost is
  `N · wires(S)` with `N ≤ (q+M)²`, hence `O((q+M)²|C|)` over the run.  The
  bracket is unaffected — the sparsified matrix still has `d_S ≤ 2W` columns, so
  the Lewis call is still `Õ(W(q+M)² + W^ω)` and `M` still obeys the paper's
  bound.  `Model/Theorem.lean` states the weaker total and says so.  *Model gap,
  not a proof convenience*: closing it needs a `Ψ`-stage in arlib's region tree,
  i.e. a product layer separate from the sum layer.

## The second entry point, for Algorithm 1

`runDense` is added at the bottom for `thm:main_fptas` (main.tex:788), the
paper's mixture-of-products theorem, whose algorithm *is* the numbered Algorithm
1 (main.tex:763–784).  It reuses `build` **unchanged** — `build` is
query-independent, and on the compiled caterpillar of `Model/Prelude.mixPair` its
candidate set is the `diagTensor` instance of `WPS.tensor`, i.e. arlib's
`WPS.hadamard`, which is Algorithm 1 lines 5–11 verbatim.  Only the output stage
differs: line 13 evaluates a **dense** `k`-vector query `w = (+α, −β)`, whereas
`run`'s single subtraction per row is specific to `a_TV`'s one `+1` and one `−1`.
Reusing `run` there would undercharge the output stage by a factor `k`, so
`runDense` is a second top-level wrapper rather than a reuse.

Line 3 of the listing, `C_0 = {(∅, 1, 1_k)}`, has no counterpart: there is no
empty region in arlib's `Region`, and Hadamard-multiplying by the all-ones
singleton is the identity, so the chain starts at the exact `Ω_1` leaf coreset.
Line 12 at `t = 1` is likewise absent — leaves are kept exact, as §4.2's "Leaf
Gates" paragraph (main.tex:888) prescribes — so the run performs `n − 1`
sparsifications where the listing performs `n`.  Both departures are recorded in
`Model/Prelude.lean` (decision 2) and in `Model/Theorem.lean`.
-/

set_option autoImplicit false

universe u

namespace TvDomainReduction.Program

open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations

/-- **The run's randomness, addressed by v-tree path.**

One draw per region of the shared v-tree; the region at path `p` reads `t p`, and
only the `L` internal regions actually use theirs.  The type is static — it does
not depend on the realised coresets — which is the shape the union bound over the
`L` steps needs. -/
abbrev Tape {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') : Type :=
  List Bool → prior.Draw

/-- **The bottom-up coreset propagation** (main.tex:888–896), by structural
recursion on the shared v-tree.

*Leaf* (P1, main.tex:888): keep the exact weighted assignment set, every
assignment with weight `1`.  No randomness, no error, `|Ω_i| ≤ q` rows.  The only
work is reading both circuits' lookup tables: `(gP + gQ) · m` stored reals.

*Product region* (P3, main.tex:896): form the candidate Cartesian product
`U_S = C_{S_h} × C_{S_ℓ}` with inherited weights `μ_ij = λ_i ρ_j`
(`WPS.tensor`), hand it to `Sparsify` with tolerance `δ` and failure `η'`
(`prior.out`), and store the result.  Exactly one sparsification per product
region, and none between the product and sum stages — the sum stage is inside
`blockTensor cP cQ` (P2, main.tex:890).

The charges, in order:
* `N` multiplications for the inherited weights `μ_ij = λ_i ρ_j`;
* `2 · N · wires` multiplications and `N · wires` additions for the features,
  where `wires = gP·gPl·gPr + gQ·gQl·gQr` is this region's coefficient-tensor
  size in *both* blocks (`blockTensor` is zero across the blocks, so the cross
  terms are never computed) — one multiply-accumulate per wire per candidate row;
* `prior.callCost N d_S` operations inside the cited Lewis-weight solver. -/
def build {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') :
    {V : Vtree} → {gP gQ : ℕ} → (P : Circuit V gP) → (Q : Circuit V gQ) →
      Tape prior → Comp (Reduction (pairRegion P Q))
  | _, _, _, @Circuit.leaf m gP θP, @Circuit.leaf _ gQ θQ, _ =>
      reads ((gP + gQ) * m)
        (Reduction.leaf (Fin m) (fun a => Sum.elim (fun j => θP j a) (fun j => θQ j a)))
  | _, _, _, @Circuit.node _ _ gPl gPr gP lP rP cP,
             @Circuit.node _ _ gQl gQr gQ lQ rQ cQ, t => do
      let Rl ← build prior lP lQ (fun p => t (false :: p))
      let Rr ← build prior rP rQ (fun p => t (true :: p))
      let N := Fintype.card Rl.Idx * Fintype.card Rr.Idx
      let wires := gP * gPl * gPr + gQ * gQl * gQr
      let U := WPS.tensor (blockTensor cP cQ) Rl.core Rr.core
      let R := Reduction.node (blockTensor cP cQ) Rl Rr _ (prior.out U (t []))
      let R ← muls (N + 2 * N * wires) R
      let R ← adds (N * wires) R
      lewisOps (prior.callCost N (gP + gQ)) R

/-- **One whole run** (main.tex:885–896), returning the bottom-up construction.

The last line of the paper's algorithm is the estimator
`D̃ = ½ ∑_j μ_j |⟨a_TV, Φ_root(z_j)⟩|` (main.tex:883).  Its arithmetic is charged
here: `a_TV` is `+1` on the `P` root coordinate and `−1` on the `Q` root
coordinate and zero elsewhere (main.tex:881), so each inner product is **one
subtraction**; then one absolute value and one multiplication by `μ_j` per
retained row, `n` additions for the outer sum, and one division by `2`.  The
estimator's *value* is `Model.Prelude.Dtilde` of the object returned; real
division is noncomputable in Lean, which is why the number is read off rather
than produced.  See the module docstring.

The whole construction is returned, not only the number, so that all three of
the theorem's claims are about one run. -/
def run {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (prior : TvDomainReduction.SparsifyPrior δ η') (t : Tape prior) :
    Comp (CircuitPair.Reduction C) := do
  let R ← build prior C.P C.Q t
  let n := Fintype.card R.Idx
  let R ← subs n R
  let R ← abses n R
  let R ← muls n R
  let R ← adds n R
  divs 1 R

/-- **One whole run of Algorithm 1** (main.tex:763–784), returning the bottom-up
construction.

`build` is reused **unchanged**: it is query-independent, and at a node of the
compiled mixture pair its candidate set `WPS.tensor (blockTensor cP cQ) …` is the
`diagTensor` instance, i.e. arlib's `WPS.hadamard`, which is exactly Algorithm 1
lines 5–11 (`U_t = C_{t-1} × Ω_t`, feature `v ⊙ r_t(x_t)`, weight `μ` inherited
unchanged because the leaf's weights are `1`).  Only the **output stage** differs
from `run`, and that is the whole reason this second entry point exists.

Algorithm 1 line 13 (main.tex:782) returns `D̃ = ½ ∑_j μ_j |wᵀ v_j|` with `w` a
**dense** `k`-vector (`+α` on the `P`-block, `−β` on the `Q`-block,
main.tex:727), so per retained row the arithmetic is `d` multiplications and
`d − 1` additions for the inner product, one absolute value, and one
multiplication by `μ_j`; then one addition per row for the outer sum and one
division by `2`.  `run`'s single subtraction per row is specific to `a_TV`, which
has one `+1` and one `−1`; reusing it here would undercharge the output stage by
a factor `d`.

`d = gP + gQ` is `Fintype.card (Coord gP gQ)`, and the number of rows is
`Fintype.card R.Idx` — the **same** quantity the existing accounting already
bounds, so this charge is to be priced through
`Analysis.TimeProof.build_card_idx_le` and
`Analysis.SpaceProof.maxInternalCard_built_le` rather than through a freshly
derived count.  The retained index types are static (the prior returns exactly
`size d` rows, zero-padded), so the tally is the same on every outcome, which is
what lets the time claim be per-outcome rather than probabilistic.

The whole construction is returned, not only the number, so that the accuracy
claim and the time claim are about one run; `Model.Prelude.DtildeMix` reads the
number off it, real division being noncomputable in Lean.  See the module
docstring. -/
def runDense {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (prior : TvDomainReduction.SparsifyPrior δ η') (t : Tape prior) :
    Comp (CircuitPair.Reduction C) := do
  let R ← build prior C.P C.Q t
  let rows := Fintype.card R.Idx
  let d := gP + gQ
  let R ← muls (rows * d + rows) R
  let R ← adds (rows * (d - 1) + rows) R
  let R ← abses rows R
  divs 1 R

/-! ## The third entry point, for weighted tree automata

`thm:wta_fpras` (main.tex:996–1003) has no numbered listing either.  Its
algorithm is spread over main.tex:967 (the normalisation DP), main.tex:969–992
(joint features, root query, estimator) and the proof main.tex:1005–1034, which
appeals to §4.2.  On `C : CircuitPair V 1 1` it is:

| paper step | Lean |
| --- | --- |
| **W1** `m_ℓ = ∑_a h_ℓ(a)`, `m_u = B_u(m_{u_L}, m_{u_R})`, `Z_R = m_r` (main.tex:967) | `massDP`, once per model; its *value* is `Model.Prelude.circuitMass` |
| **W3** zero-padding to dimension `d` (main.tex:1006) | none: arlib allows per-node dimensions |
| **W4** unary root sum gate of weight `Z_R^{-1}` (main.tex:1006) | folded into the root query `aWTA = (Z_P^{-1}, −Z_Q^{-1})` (main.tex:984): 2 inversions and 1 negation |
| **W5** scalar product/sum-gate expansion (main.tex:1008–1030) | none: `Circuit.node` is the bilinear gate (`valP_node` = main.tex:953) |
| **W6** exact leaf coreset (main.tex:888) | `build`, leaf branch, unchanged |
| **W7** product, then **one** `Sparsify` per internal node at `(ε/(3I), η/I)` (main.tex:896) | `build`, node branch, unchanged |
| **W8** `d̂ = ½ ∑ μ |v_P/Z_P − v_Q/Z_Q|` (main.tex:992, 997) | `runDense` with `gP = gQ = 1` (dense 2-vector query); value `Model.Prelude.DtildeWTA` |

`build` is reused unchanged, which carries the circuit theorem's fused-node model
gap over: the post-gate features (`≤ d³` wires) are formed on every candidate
row, where the paper's expanded circuit pays `d²` per candidate row and the
`d³`-wire sum layer on the survivors only.  `Model/Theorem.lean`'s
`wta_fpras_time` states the bound this accounting supports. -/

/-- **The normalisation DP** (main.tex:967), charged, for one automaton.

At a leaf with `g` coordinates over `Fin m`: `g · (m − 1)` additions for
`m_ℓ = ∑_a h_ℓ(a)`.  At an internal node: both children first, then for each of
the `g · gl · gr` tensor entries two multiplications and one addition, for
`[m_u]_i = ∑_j ∑_k T_{u,i,j,k} [m_{u_L}]_j [m_{u_R}]_k`.  The value is not produced
here (real arithmetic is read off as `Model.Prelude.circuitMass`); the operations
that produce it are paid for, and the argument `a` is passed through untouched so
that the charge can be sequenced in any `Comp` block. -/
def massDP {α : Type u} : {V : Vtree} → {g : ℕ} → Circuit V g → α → Comp α
  | _, _, @Circuit.leaf m g _, a => adds (g * (m - 1)) a
  | _, _, @Circuit.node _ _ gl gr g l r _, a => do
      let a ← massDP l a
      let a ← massDP r a
      let a ← muls (2 * g * gl * gr) a
      adds (g * gl * gr) a

/-- **One whole run of the WTA algorithm** (§5, main.tex:961–1034), returning the
bottom-up construction.

First the normalisation DP for both automata (W1), then the two query entries
`Z_P^{-1}` and `−Z_Q^{-1}` (2 divisions and 1 negation, charged as a
subtraction from `0`), then `runDense` **unchanged**: `build` on the joint pair
(W6, W7) and the dense root evaluation, which with `gP = gQ = 1` is exactly two
multiplications and one addition per retained row for `⟨a_TV, v⟩`, then one
absolute value, one multiplication by `μ_j`, one addition, and the final division
by `2` (W8).  `Program.run` is not reused: its single subtraction per row is
priced for the `±1` query and it omits the DP.

The whole construction is returned so that the accuracy and time claims of
`thm:wta_fpras` are about one run; `Model.Prelude.DtildeWTA` reads `d̂` off it. -/
def runWTA {δ η' : ℝ} {V : Vtree} (C : CircuitPair V 1 1)
    (prior : TvDomainReduction.SparsifyPrior δ η') (t : Tape prior) :
    Comp (CircuitPair.Reduction C) := do
  let u : PUnit.{2} := PUnit.unit
  let u ← massDP C.P u
  let u ← massDP C.Q u
  let u ← divs 2 u
  let _ ← subs 1 u
  runDense C prior t

#programSeal TvDomainReduction.Program
#executableModule TvDomainReduction.Model.Program
#surplusIn TvDomainReduction.Model.Program from run runDense runWTA

end TvDomainReduction.Program
