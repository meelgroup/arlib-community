import TvDomainReduction.Interface.Encoding

/-!
# The bottom-up coreset propagation as mathematics

§4.2 of the paper (main.tex:885–896) written a second time: not as a charged
program over a tape, but as a **law over the object the correctness proof is
about**.  `Model/Program.lean` is the algorithm as something that *costs*;
this file is the same algorithm as something a `PMF` and an induction over the
v-tree can be run on.  The bridge between them is the next file
(`Interface/ProgramModel.lean`); nothing here is proved about the paper's result,
and nothing here mentions time or space.

## Why there are two definitions of one algorithm

It is not about computability: every real-valued definition on either side is
already noncomputable, and `Model/Program.lean`'s payload is reached through
`Charged.val`, which is noncomputable on purpose.  The reason is that
**`Arlib.Computation.Charged` is a sealed, non-extensional carrier**, and
deliberately so.  Its constructor is `private`; the only ways to build one are
`pure`, `bind` and `Charged.op`, so the tally is a function of the program's
*text* and cannot be written down beside it.  The price of that guarantee is that
a `Charged` value holds an **ordered history** — a `CostVec` and a `Profile`
accumulated in the order the `bind`s were written — and two charged values
carrying the *same* `Reduction` by different histories are different terms.  The
expensive operation of this algorithm genuinely *is* the iteration the history
records: forming `(q+M)²` candidate rows at a product region and paying for each.
That is the cost claim, and it is right that the program side cannot abstract it.

The correctness claim is about none of it.  Claim (1) of Theorem 4.1 compares two
*laws of values*: the law of `D̃` against the fixed number `d_TV(P,Q)`.  So the
pseudocode side quotients away both the tally and the tape:

| | `Model/Program.lean` + `Model/Run.lean` | here |
| --- | --- | --- |
| the run's randomness | a whole `Tape prior = List Bool → prior.Draw`, drawn up front by `Run.tapeLaw` | drawn lazily, one `prior.law` call per product region, inside `reduceLaw` |
| what a run is | `Comp (CircuitPair.Reduction C)` — value **and** tally **and** profile | `Reduction (pairRegion P Q)` — the construction alone |
| the law of a run | `PMF (Comp (CircuitPair.Reduction C))` | `PMF (Reduction (pairRegion P Q))` |

The two laws are the same distribution over constructions — drawing a tape and
then reading the construction off it is drawing the construction — and that
equality is the bridge's statement, `Pseudocode.runLaw = (Run.runLaw …).map
Interface.runOutcome`.  The lazy form is what makes the union bound of
main.tex:926 an induction on the v-tree: at a product region `reduceLaw` is
literally `bind` of the two children's laws with one `prior.law` call, so
`PMF.toOuterMeasure_bind_apply` and `SparsifyPrior.bad_prob` meet without any
reasoning about `Run.graft`, about tape addresses, or about `Charged.bind`'s
tally.

Doing the same induction over `Run.tapeLaw` is possible and strictly harder: the
event "all `L` sparsifications succeeded" is a predicate of the construction, so
every step of it would have to push `Interface.built` through a `graft`.  That is
the whole of what this file buys.

## Correspondence ledger (algorithm transcript → pseudocode → program)

There is **no numbered algorithm listing for the circuit case** — Algorithm 1
(main.tex:763–784) is the mixture case.  §4.2 is three paragraphs of prose, so
this ledger is the whole of the claim that the two columns below are the paper's
algorithm.

| transcript step | paper | pseudocode (this file) | program it bridges to |
| --- | --- | --- | --- |
| **P0** parameters `δ = ε/(3L)`, `η' = η/L`, budget `m` | main.tex:886 | `StepPrior` (and `TvDomainReduction.perStepTol` / `perStepFail`, `SparsifyPrior.size`) | the `prior` argument of `Program.build`; `Interface.RetainedIdx` |
| **P1** leaf: keep the exact set `{(a,1,Φ_{{i}}(a)) : a ∈ Ω_i}` | main.tex:888 | `leafCoreset` | `Program.build`'s leaf branch; `Interface.built_leaf` |
| **P2** sum layer: a fixed linear map, free, no domain growth | main.tex:890–894 | *no declaration of its own* — `Arlib.Approximation.WPS.linMap`, fused into `blockTensor`; see `MODEL:` (a) | fused into `Program.build`'s `blockTensor cP cQ` |
| **P3** product region: `U_S = C_{S_h} × C_{S_ℓ}`, `μ_ij = λ_i ρ_j`, evaluate `Ψ_S`, call `Sparsify(·,m,η')` | main.tex:896 | `Interface.candidates` then `productCoreset` | `Program.build`'s node branch; `Interface.built_node` |
| **S0** `Sparsify`, cited not proved | main.tex:745, 761 | `sparsify` (`prior.law`, then `prior.out`) | `prior.out U (t [])` inside `Program.build`, with `Run.tapeLaw` supplying `prior.law` |
| the bottom-up run | main.tex:885 | `reduceLaw`, `runLaw` | `Program.build`, `Run.runLaw` |
| **P4** output `D̃ = ½ ∑_j μ_j |⟨a_TV, Φ_root(z_j)⟩|` | main.tex:883 | `answerLaw` (of `TvDomainReduction.Dtilde`) | `Run.answerLaw`, `Interface.answer` |
| "all `L` sparsifications succeeded" | main.tex:926 | `Arlib.Approximation.Reduction.Sparsifies δ` of a point of `runLaw` | the same predicate; it is a property of the construction, so the two sides share it |

`Dtilde`, `aTV`, `perStepTol`, `perStepFail` and `SparsifyPrior` are **not**
redefined here: they are `Model/Prelude.lean`'s, because a second copy of the
estimator or of the root query would be a second claim.  Likewise `candidates`
and `RetainedIdx` are `Interface/Encoding.lean`'s, so that `built_node` and
`reduceLaw_node` mention one term and not two.

## `MODEL:` gaps — places the program is not the transcript

These are recorded in `Model/Program.lean` and `Model/Theorem.lean` as well.  They
are repeated here because this is the file a reader holds against the prose, and
because a mirror that reproduced them silently would make them look intentional
on the paper's side.

* **`MODEL:` (a) the `Ψ` stage has no separate existence.**  main.tex:894
  sparsifies the product-stage features `Ψ_S` and *then* applies the same-scope
  linear map `L_S` **to the surviving rows only**.  arlib's `Region.node` carries
  one bilinear tensor per region, and `blockTensor cP cQ` is the *fused*
  product-then-sum tensor, so `Interface.candidates` is already the post-sum
  candidate set and `productCoreset` performs the paper's two stages as one
  `Sparsify` call.  Two consequences, in opposite directions:
  - *harmless for claim (1).*  A `Ψ`-stage `(1 ± δ)` embedding implies the fused
    one with the same window, because the fused candidate set is
    `WPS.linMap L_S` of the `Ψ`-stage one and `Arlib.Approximation.Embeds.linMap`
    says a linear reparametrisation is free.  The per-step hypothesis used here is
    therefore *weaker* than the paper's.
  - *not harmless for claim (3).*  Because `L_S` is applied to every candidate row
    rather than to the survivors, the circuit-traversal term of the running time
    is `(q+M)²|C|` where the paper has `(q+M)|C|`.  That term is a program-side
    claim and this file does not state it; `Model/Theorem.lean` states the weaker
    total and says so.  Closing the gap needs a `Ψ`-stage in arlib's region tree,
    i.e. a product layer separate from the sum layer.
* **`MODEL:` (b) every internal v-tree node is a product region.**  The paper's
  `L` counts only *active* ones — those where at least one circuit has a product
  gate (main.tex:886).  `Region.steps`, which is what `reduceLaw` recurses over
  and what `Reduction.Sparsifies` quantifies, counts all of them, so the Lean `L`
  is `≥` the paper's.  Accuracy is unaffected (a larger `L` means a smaller `δ`);
  both resource claims are weakened.  A statement decision, taken in
  `Model/Theorem.lean`.
* **`MODEL:` (c) `Sparsify` returns exactly `prior.size d` rows, zero-padded,
  rather than "at most `m`".**  main.tex:748 bounds the number of *nonzero*
  entries of the sampling matrix.  Padding keeps every index type static, which is
  what lets `reduceLaw` be an ordinary `bind` instead of a dependent product over
  random sizes — see decision 2 of `SparsifyPrior`'s docstring.  Nothing is
  claimed about the padded rows; they carry weight `0` by whatever instantiation
  supplies them.
* **`MODEL:` (d) the `L = 0` case is out of scope.**  main.tex:886 carves it out
  ("Sparsify is never called and the TV-distance can be computed deterministically
  and exactly").  `reduceLaw` is total and does the right thing there — a
  single-leaf v-tree gives `PMF.pure (leafCoreset …)`, the exact answer — but
  `δ = ε/(3L)` is undefined at `L = 0`, so the theorem assumes `0 < L` and this
  file makes no claim about that case either.

## What this file deliberately does not contain

* **No meter.**  No time, space, candidate-count or draw-count field anywhere.
  Those are operators applied to `Model/Program.lean`'s charged term
  (`Interface.opCount`, `Interface.retainedPeak`), and a number pinned to itself
  in two places is invisible when it is wrong.
* **No bridging arithmetic.**  There is none to carry: the program's answer is
  already the paper's real number (`Dtilde` of the returned construction), so
  there is no integer-to-real cast to discharge and this file states no lemma
  with a tactic proof.
* **No proof devices of the analysis.**  The relaxed and idealised processes the
  argument compares `reduceLaw` against — a run conditioned on success, a run with
  the exact sets substituted — belong to the agents that need them.
* **Nothing executable.**  `reduceLaw` and `sparsify` are `noncomputable` because
  they mention `PMF`; `leafCoreset` and `productCoreset`'s non-random part are
  not, which is an accident of them containing no real division, not an invitation
  to run them.  This side is never run: it is what the program is *compared to*.
-/

set_option autoImplicit false

namespace TvDomainReduction.Pseudocode

open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic

/-! ## P0 — the parameters (main.tex:886)

The algorithm's own parameter choice is `δ = ε/(3L)` and `η' = η/L`, and the only
way those two numbers reach the pseudocode is as the *index of the `Sparsify`
prior*: a call is made with tolerance `δ` and failure probability `η'` exactly
when the prior it is made against is a `SparsifyPrior δ η'`.  `StepPrior` names
that instantiation, so the correspondence ledger has one declaration to point at
and the recursion below needs no `ε`, `η` or `L` argument of its own.

The remaining P0 read-offs — `q` (`leafDomMax`), `W` (`pairWidth`), `|C|`
(`pairSize`), `L` (`CircuitPair.steps`) and the row budget `m`
(`SparsifyPrior.size`) — are `Model/Prelude.lean`'s and are not restated.  Only
`m` is visible to the algorithm at all, through the index type the prior returns
(`Interface.RetainedIdx`); the other three are static read-offs that the resource
claims mention and the algorithm never consults. -/

/-- **P0** (main.tex:886).  The `Sparsify` prior the algorithm calls when its
inputs are `ε`, `η` and a v-tree with `L` product regions: per-step tolerance
`δ = ε/(3L)` and per-step failure probability `η' = η/L`.

This is the shape `Model/Theorem.lean` carries in its binder list, named once. -/
abbrev StepPrior (ε η : ℝ) (L : ℕ) : Type 1 :=
  TvDomainReduction.SparsifyPrior (TvDomainReduction.perStepTol ε L)
    (TvDomainReduction.perStepFail η L)

/-! ## S0 — `Sparsify`, as the one random step (main.tex:745, 761)

The paper specifies `Sparsify(U, m, η')` contractually and instantiates it by
Theorem `thm:lewis_weights`, which it **cites** rather than proves; so does this
development, through `TvDomainReduction.SparsifyPrior`.

`sparsify` is where the pseudocode draws *lazily*: `Model/Run.lean` draws a whole
tape and `Model/Program.lean` then applies `prior.out` to the draw addressed to
this region, whereas here the output set is drawn directly, from the pushforward
of `prior.law U` along `prior.out U`.  Those are the same distribution — one is
the image of the other under a measurable map that is a plain function — and the
bridge proof is shorter for it. -/

/-- **S0** (main.tex:761): one `Sparsify` call on the candidate set `U`.

The law is `prior.law U`, *the law of a call on the matrix this region actually
sees*, which is what makes the per-step failure bound conditional on the history
and hence composable (`SparsifyPrior.bad_prob` is quantified over every candidate
set; see decision 1 of its docstring).  The output has exactly
`prior.size (card d)` rows, zero-padded — `MODEL:` (c). -/
noncomputable def sparsify {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {κ d : Type} [Fintype κ] [Fintype d] (U : WPS κ d) :
    PMF (WPS (Fin (prior.size (Fintype.card d))) d) :=
  (prior.law U).map (prior.out U)

/-! ## P1 — leaf regions (main.tex:888)

"For a leaf variable `X_i` with domain `Ω_i`, we enumerate the exact weighted
assignment set `C_{{i}} = {(a, 1, Φ_{{i}}(a)) : a ∈ Ω_i}`."

No randomness, no error, no sparsification, and `|Ω_i| ≤ q` rows.  That the
weights are all `1` and the features are the two circuits' leaf tables
concatenated is `Arlib.Approximation.Reduction.core_leaf` together with
`Region.exactWPS`: the construction stored at a leaf *is* the unreduced set. -/

/-- **P1** (main.tex:888): the exact weighted assignment set at a leaf region,
`P`-block then `Q`-block.

This is the base case of the propagation invariant, and the reason leaf regions
contribute no error and the complexity bound carries `q` separately from `M`. -/
def leafCoreset {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ) :
    Reduction (pairRegion (Circuit.leaf θP) (Circuit.leaf θQ)) :=
  Reduction.leaf (Fin m) (fun a => Sum.elim (fun j => θP j a) (fun j => θQ j a))

/-! ## P2 — sum layers are free (main.tex:890–894)

"Collecting the sum gates of both circuits therefore gives a block-diagonal
linear transformation `L_S` of the existing features … Because `C_S` preserves
all linear tests on `Φ_S^old`, it preserves all linear tests on `Φ_S^new` without
introducing additional error or domain expansion."

**This step has no declaration of its own in this file, on purpose.**  The
operation is `Arlib.Approximation.WPS.linMap` and the statement that it is free is
`Arlib.Approximation.Embeds.linMap`; defining a project-local alias for either
would be a duplicate that every later proof has to bridge back by hand.  In the
recursion below the map is not applied separately at all: `blockTensor cP cQ`
is already the fused product-then-sum tensor, so `Interface.candidates` carries
the post-sum features.  That is `MODEL:` (a), and `Embeds.linMap` is the recorded
justification that the fused per-step hypothesis is implied by the paper's
`Ψ`-stage one. -/

/-! ## P3 — active product regions (main.tex:896)

"Given reduced child domains `C_{S_h}` and `C_{S_ℓ}`, we form the candidate
Cartesian product domain `U_{S_g} = C_{S_h} × C_{S_ℓ}` containing
`N = m_{S_h} m_{S_ℓ}` pairs `z_ij = (u_i, v_j)` with inherited weights
`μ_ij = λ_i ρ_j`.  For every candidate pair, we evaluate `Ψ_{S_g}(z_ij)` and
apply Theorem `thm:lewis_weights` with parameters `δ` and `η'` … Applying the
same-scope linear map to the surviving rows yields the coreset `C_{S_g}`."

The candidate set is `Interface.candidates`, i.e. `WPS.tensor (blockTensor cP cQ)`
of the two children's cores: indices pair up, **weights multiply** (`WPS.tensor`'s
`wt` field is `λ_i · ρ_j`), features combine bilinearly through the region's
tensor — which is what decomposability buys.  Exactly one `Sparsify` call per
product region, and none between the product and sum stages. -/

/-- **P3** (main.tex:896): one active product region.

Form the candidate Cartesian product of the two children's coresets, hand it to
`Sparsify` with this region's parameters, and store the surviving rows as the
node's reduced set.  The children are already drawn; this is the step's own
randomness and the one event the union bound of main.tex:926 counts at this
region. -/
noncomputable def productCoreset {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {Vl Vr : Vtree} {gPl gPr gP gQl gQr gQ : ℕ}
    {lP : Circuit Vl gPl} {rP : Circuit Vr gPr}
    {lQ : Circuit Vl gQl} {rQ : Circuit Vr gQr}
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ)
    (Rl : Reduction (pairRegion lP lQ)) (Rr : Reduction (pairRegion rP rQ)) :
    PMF (Reduction (pairRegion (Circuit.node lP rP cP) (Circuit.node lQ rQ cQ))) :=
  (sparsify prior (Interface.candidates cP cQ Rl Rr)).map
    (fun C => Reduction.node (blockTensor cP cQ) Rl Rr
      (Interface.RetainedIdx prior gP gQ) C)

/-! ## The run — bottom-up along the common v-tree (main.tex:885)

The recursion is structural on the shared v-tree and matches on **both** circuits
at once, which only typechecks because they are indexed by the same `V`: at a
v-tree leaf both are leaf circuits, at a v-tree node both are nodes.  That shared
index *is* the paper's "structured with respect to a common v-tree" hypothesis,
and it is also what makes the region graph a tree rather than a DAG — the
hypothesis that lets the single number `L` be both the window exponent and the
number of union-bound events.

The draws are taken bottom-up, children before parent, so the candidate set a
region's `prior.law` is applied to is the realised one.  `Model/Run.lean`'s
`tapeLaw` draws in the same order (`tl`, then `tr`, then this region's `x`), which
is what the bridge needs. -/

/-- **The bottom-up coreset propagation** (main.tex:885–896), as a law over
constructions.

`PMF.pure (leafCoreset …)` at a leaf (P1), and at a product region the `bind` of
the two children's laws with one `productCoreset` call (P3).  The number of
`prior.law` calls along any point of the support is `Region.steps`, the paper's
`L` — see `MODEL:` (b). -/
noncomputable def reduceLaw {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') :
    {V : Vtree} → {gP gQ : ℕ} → (P : Circuit V gP) → (Q : Circuit V gQ) →
      PMF (Reduction (pairRegion P Q))
  | _, _, _, @Circuit.leaf m gP θP, @Circuit.leaf _ gQ θQ =>
      PMF.pure (leafCoreset θP θQ)
  | _, _, _, @Circuit.node _ _ _ _ _ lP rP cP,
             @Circuit.node _ _ _ _ _ lQ rQ cQ => do
      let Rl ← reduceLaw prior lP lQ
      let Rr ← reduceLaw prior rP rQ
      productCoreset prior cP cQ Rl Rr

/-- The leaf equation of `reduceLaw`, in the shape an induction over the v-tree
rewrites with.  The counterpart of `Interface.built_leaf`. -/
theorem reduceLaw_leaf {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ) :
    reduceLaw prior (Circuit.leaf θP) (Circuit.leaf θQ)
      = PMF.pure (leafCoreset θP θQ) := rfl

/-- The product-region equation of `reduceLaw`: the two children first, then this
region's own `Sparsify` call.  The counterpart of `Interface.built_node` and of
`Interface.tapeLaw_node`. -/
theorem reduceLaw_node {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {Vl Vr : Vtree} {gPl gPr gP gQl gQr gQ : ℕ}
    (lP : Circuit Vl gPl) (rP : Circuit Vr gPr)
    (lQ : Circuit Vl gQl) (rQ : Circuit Vr gQr)
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ) :
    reduceLaw prior (Circuit.node lP rP cP) (Circuit.node lQ rQ cQ)
      = (reduceLaw prior lP lQ >>= fun Rl =>
          reduceLaw prior rP rQ >>= fun Rr =>
            productCoreset prior cP cQ Rl Rr) := rfl

/-- **One whole run on a circuit pair** (main.tex:885).

The law of the bottom-up construction the algorithm leaves behind at every region.
The construction and not only the number, so that the invariant of
`lem:pc_invariant` — which is a statement about every region at once — is a
statement about a point of *this* support. -/
noncomputable def runLaw {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') :
    PMF (CircuitPair.Reduction C) :=
  reduceLaw prior C.P C.Q

/-! ## P4 — the output (main.tex:883)

"Therefore the root coreset yields the estimator
`D̃ := ½ ∑_{j=1}^{m_root} μ_j |⟨a_TV, Φ_root(z_j)⟩|`."

That is `TvDomainReduction.Dtilde` of the root construction, at the root query
`TvDomainReduction.aTV jP jQ` — `+1` on the designated `P` root gate, `−1` on the
designated `Q` root gate, `0` elsewhere.  Neither is redefined here: a second copy
of the estimator or of the root query would be a second claim, and a sign slip in
it would be invisible in the build and fatal.

`answerLaw` is **the answer object this interface exists to transport**: claim (1)
of the theorem is a measure of it, and the bridge's job is to identify it with
`Run.answerLaw`, which is the same pushforward taken over the charged run. -/

/-- **P4** (main.tex:883): the law of the estimator `D̃` produced by one run.

The pseudocode-side counterpart of `Run.answerLaw`, and the distribution claim (1)
of Theorem 4.1 is a measure of. -/
noncomputable def answerLaw {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    (jP : Fin gP) (jQ : Fin gQ) : PMF ℝ :=
  (runLaw C prior).map (fun R => TvDomainReduction.Dtilde R jP jQ)

end TvDomainReduction.Pseudocode
