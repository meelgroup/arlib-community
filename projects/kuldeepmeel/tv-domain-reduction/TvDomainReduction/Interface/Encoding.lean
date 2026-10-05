import TvDomainReduction.Model.Run

/-!
# The specification's view of the run

`Model/` says what Theorem 4.1 claims and how the algorithm is written; `Analysis/`
proves the claim.  The two speak different dialects, and this file is the
dictionary between them.  It holds no mathematics: **every lemma below is `rfl`**,
and anything that is not `rfl` is a claim and belongs in
`TvDomainReduction/Interface/ProgramModel.lean` with a proof.

It does three things and nothing else.

## 1. Collapse the currency indirection

`Model/Program.lean` is written against the charged wrappers of
`Model/Operations.lean` (`adds`, `muls`, `reads`, `lewisOps`, …) while the
running-time claim in `Model/Theorem.lean` is stated with
`Arlib.Computation.Charged.steps rate`.  The wrappers are *definitionally*
`Charged.opMany` and `rate` is *definitionally* `Rate.unit ArithOp`, but neither
pair is syntactically equal, which is enough to stop `simp` and `omega` dead.
`rate_cost` and the seven `…_eq_opMany` lemmas below are what re-connect them;
after them arlib's own `@[simp]` lemmas (`Charged.steps_opMany`,
`Charged.steps_bind`) fire on the program's text.

There is one lemma per *wrapper* here rather than one per class, and that is a
consequence of a deliberate decision in `Model/Operations.lean`: this development
declares its own work currency `ArithOp`, because the paper counts arithmetic
operations on reals (main.tex:904, main.tex:147) and arlib's `StdOp` is the
vocabulary of its sealed word-level containers.  So there is no `RosterOps`-style
class indirection to collapse — there is a wrapper layer instead, and this is its
collapse.

## 2. Name the specification's views of a run

`Program.run` returns a `Charged` value whose payload is sealed behind the
noncomputable `Charged.val`.  The three claims of the theorem are three operators
applied to that one object, and each wants a different read of it:

| claim | view |
| --- | --- |
| (1) accuracy, main.tex:902 | `answer` — the estimator `D̃` of main.tex:883 |
| (2) retained size, main.tex:905 | `retainedPeak` — the observed `M` |
| (3) arithmetic time, main.tex:904 | `opCount` — `Charged.steps` in `ArithOp` |
| the object all three are about | `runOutcome` / `built` — the `Reduction` |

`built` is the single most useful of them: it is the bottom-up construction with
the charges forgotten, so `built_leaf` and `built_node` give the analysis the
recursion that `Reduction.Sparsifies` and `maxInternalCard` are stated over,
without ever reasoning about the tally.  These reads are `noncomputable`, and
that is the point — a view is right for an invariant and wrong for a line of the
algorithm.  Executable algorithm code stays governed by `#programSeal` in
`Model/Program.lean`; nothing in this file creates a charge.

**The answer object** this interface transports is `answer`: `answerLaw_eq_map`
says the distribution claim (1) is a measure of is exactly the pushforward of the
run's law along it.

## 3. Give the proofs handles on `Model/` subterms

`candidates` is the paper's `U_S = C_{S_h} × C_{S_ℓ}` (main.tex:896) as a name, so
that `built_node` and the per-step `Sparsify` hypothesis mention the same term;
`RetainedIdx` is the static index type the prior returns, so that the size claim
has something to take `Fintype.card` of.  The remaining lemmas are the defining
equations of the `Model/` recursions, which the elaborator does not export as
`simp` lemmas in the shape an induction wants.

## Correspondence with the algorithm transcript (main.tex:885–896)

There is no numbered listing for the circuit case; the algorithm is prose.  The
transcript's steps land here as follows.

| transcript step | paper | here |
| --- | --- | --- |
| **P0** parameters `q, W, L, δ = ε/(3L), η' = η/L, m` | main.tex:886 | `leafDomMax_*`, `pairWidth_eq`, `perStepTol_eq`, `perStepFail_eq`, `RetainedIdx` |
| **P1** leaf: the exact set `{(a,1,Φ(a)) : a ∈ Ω_i}` | main.tex:888 | `built_leaf` |
| **P2** sum layer: a fixed linear map, free | main.tex:890 | *fused* into `blockTensor cP cQ`; see below |
| **P3** product region: `U_S = C_{S_h} × C_{S_ℓ}`, `μ_ij = λ_i ρ_j`, then `Sparsify(·,m,η')` | main.tex:896 | `candidates`, `built_node` |
| **P4** output `D̃ = ½ ∑_j μ_j |⟨a_TV, Φ_root(z_j)⟩|` | main.tex:883 | `answer`, `answer_run`, `Dtilde_eq` |
| **S0** `Sparsify` / `thm:lewis_weights`, cited not proved | main.tex:745, 761 | `prior.out`, appearing in `built_node` |
| the `L` draws and their joint law | main.tex:926 | `graft_*`, `tapeLaw_leaf`, `tapeLaw_node` |

Two places where the transcript and `Model/Program.lean` genuinely differ, both
recorded in `Model/`'s own docstrings and repeated here because this is the file a
reader compares against the prose:

* **The `Ψ` stage is invisible.**  main.tex:894 sparsifies the product-stage
  features `Ψ_S` and *then* applies the same-scope linear map `L_S` to the
  surviving rows.  arlib's `Region.node` fuses product-then-sum into one bilinear
  tensor, so `candidates` is already the post-sum candidate set and the single
  `prior.out` call in `built_node` is the fused step.  A `Ψ`-stage `(1 ± δ)`
  embedding implies the fused one with the same window (`Embeds.linMap`), so the
  per-step hypothesis used here is *weaker* than the paper's.  What is lost is the
  visibility of the paper's column count — "the product-stage feature matrix has
  `O(W)` columns", main.tex:929 — which is why `RetainedIdx` is indexed by
  `Fintype.card (Coord gP gQ)` and not by a separate `Ψ`-dimension.
* **Every internal v-tree node is a product region.**  The paper's `L` counts only
  *active* ones (main.tex:886); `CircuitPair.steps` counts all of them, so the
  Lean `L` is `≥` the paper's.  Nothing in this file repairs that; it is a
  statement decision taken in `Model/Theorem.lean`.

Nothing here is mentioned by a headline statement, and nothing here is proved
about the paper's result.
-/

set_option autoImplicit false

namespace TvDomainReduction.Interface

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations

universe u

/-! ## 1. The currency, collapsed

`Model/Operations.lean` prices the program through seven wrappers over
`Charged.opMany`, under the unit rate.  These eight `rfl` lemmas are the whole of
the translation; with them, `Charged.steps_opMany` and `Charged.steps_bind` reduce
`Charged.steps rate (Program.run …)` to arithmetic on `ℕ`. -/

/-- **Every arithmetic operation costs one** (main.tex:904).  `rate` is
`Rate.unit ArithOp` by definition, but not syntactically, so `Rate.unit_cost`
does not fire on it. -/
@[simp] theorem rate_cost (o : ArithOp) : rate.cost o = 1 := rfl

@[simp] theorem adds_eq_opMany {α : Type u} (n : ℕ) (a : α) :
    adds n a = Charged.opMany ArithOp.add n a := rfl

@[simp] theorem subs_eq_opMany {α : Type u} (n : ℕ) (a : α) :
    subs n a = Charged.opMany ArithOp.sub n a := rfl

@[simp] theorem muls_eq_opMany {α : Type u} (n : ℕ) (a : α) :
    muls n a = Charged.opMany ArithOp.mul n a := rfl

@[simp] theorem divs_eq_opMany {α : Type u} (n : ℕ) (a : α) :
    divs n a = Charged.opMany ArithOp.div n a := rfl

@[simp] theorem abses_eq_opMany {α : Type u} (n : ℕ) (a : α) :
    abses n a = Charged.opMany ArithOp.abs n a := rfl

@[simp] theorem reads_eq_opMany {α : Type u} (n : ℕ) (a : α) :
    reads n a = Charged.opMany ArithOp.lit n a := rfl

@[simp] theorem lewisOps_eq_opMany {α : Type u} (n : ℕ) (a : α) :
    lewisOps n a = Charged.opMany ArithOp.lewis n a := rfl

/-! ## 2. The specification's views of a run -/

/-- **The bottom-up construction a tape produces, with the charges forgotten**
(main.tex:888–896).

`Program.build` returns a `Charged` value; this is its payload.  `noncomputable`,
because `Charged.val` is — and deliberately so: the invariant of
`lem:pc_invariant` is a statement about *this*, while the algorithm may only get
at it by binding, which pays. -/
noncomputable def built {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {V : Vtree} {gP gQ : ℕ} (P : Circuit V gP) (Q : Circuit V gQ)
    (t : Program.Tape prior) : Reduction (pairRegion P Q) :=
  (Program.build prior P Q t).val

/-- **The whole run's construction**: the `Reduction` the paper's algorithm leaves
behind at every region, read off one charged run. -/
noncomputable def runOutcome {V : Vtree} {gP gQ : ℕ}
    {C : CircuitPair V gP gQ} (p : Comp (CircuitPair.Reduction C)) :
    CircuitPair.Reduction C :=
  p.val

/-- **The answer object**: the estimator `D̃ = ½ ∑_j μ_j |⟨a_TV, Φ_root(z_j)⟩|`
(main.tex:883) read off a charged run.

This is the pseudocode-side value that claim (1) is transported onto:
`answerLaw_eq_map` says `Run.answerLaw` is its pushforward. -/
noncomputable def answer {V : Vtree} {gP gQ : ℕ} {C : CircuitPair V gP gQ}
    (jP : Fin gP) (jQ : Fin gQ) (p : Comp (CircuitPair.Reduction C)) : ℝ :=
  TvDomainReduction.Dtilde (runOutcome p) jP jQ

/-- **The observed `M`** (main.tex:905): the largest number of rows retained at
any internal region of one charged run. -/
noncomputable def retainedPeak {V : Vtree} {gP gQ : ℕ}
    {C : CircuitPair V gP gQ} (p : Comp (CircuitPair.Reduction C)) : ℕ :=
  TvDomainReduction.maxInternalCard (runOutcome p)

/-- **The arithmetic running time of one run** (main.tex:904), in the unit rate of
`Model/Operations.lean`.  `noncomputable` like the other views: an algorithm may
not read its own meter, and `Charged.cost` is on `forbiddenInProgram` for exactly
that reason. -/
noncomputable def opCount {α : Type u} (p : Comp α) : ℕ := Charged.steps rate p

/-- The unfolding of `built`.  Deliberately **not** `@[simp]`: the normal form the
analysis wants is `built`, because that is what `built_leaf`/`built_node` recurse
on and what `tapeLaw_node` mentions.  `Model/Run.lean` writes
`(Program.build …).val` literally, so this is the lemma that folds it up. -/
theorem built_eq {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {V : Vtree} {gP gQ : ℕ} (P : Circuit V gP) (Q : Circuit V gQ)
    (t : Program.Tape prior) :
    built prior P Q t = (Program.build prior P Q t).val := rfl

/-- Likewise not `@[simp]`: it would fire before `runOutcome_run` and leave a
`Charged.val` the recursion cannot see through. -/
theorem runOutcome_eq {V : Vtree} {gP gQ : ℕ}
    {C : CircuitPair V gP gQ} (p : Comp (CircuitPair.Reduction C)) :
    runOutcome p = p.val := rfl

@[simp] theorem opCount_eq {α : Type u} (p : Comp α) :
    opCount p = Charged.steps rate p := rfl

/-- The charges `Program.run` adds on top of `Program.build` for the root
evaluation (main.tex:883) do not touch the construction: every one of them is an
`opMany`, whose value is its argument. -/
@[simp] theorem runOutcome_run {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ}
    (C : CircuitPair V gP gQ) (prior : TvDomainReduction.SparsifyPrior δ η')
    (t : Program.Tape prior) :
    runOutcome (Program.run C prior t) = built prior C.P C.Q t := rfl

@[simp] theorem answer_run {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ}
    (C : CircuitPair V gP gQ) (prior : TvDomainReduction.SparsifyPrior δ η')
    (t : Program.Tape prior) (jP : Fin gP) (jQ : Fin gQ) :
    answer jP jQ (Program.run C prior t)
      = TvDomainReduction.Dtilde (built prior C.P C.Q t) jP jQ := rfl

@[simp] theorem retainedPeak_run {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ}
    (C : CircuitPair V gP gQ) (prior : TvDomainReduction.SparsifyPrior δ η')
    (t : Program.Tape prior) :
    retainedPeak (Program.run C prior t)
      = TvDomainReduction.maxInternalCard (built prior C.P C.Q t) := rfl

/-- **The law of the run**, as the pushforward of the tape law along the program.
The definition of `Run.runLaw`, named so a proof can rewrite with it. -/
theorem runLaw_eq_map {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (prior : TvDomainReduction.SparsifyPrior δ η') :
    Run.runLaw C prior
      = (Run.tapeLaw prior C.P C.Q).map (fun t => Program.run C prior t) := rfl

/-- **The distribution claim (1) is about is the pushforward of the run's law along
the answer object.**  This is the transport the interface exists for. -/
theorem answerLaw_eq_map {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (prior : TvDomainReduction.SparsifyPrior δ η') (jP : Fin gP) (jQ : Fin gQ) :
    Run.answerLaw C prior jP jQ = (Run.runLaw C prior).map (answer jP jQ) := rfl

/-! ## 3. Handles on `Model/` subterms -/

/-! ### The candidate set and the retained index type -/

/-- **`U_S = C_{S_h} × C_{S_ℓ}`, with inherited weights `μ_ij = λ_i ρ_j`**
(main.tex:896): the candidate Cartesian-product domain handed to `Sparsify` at a
product region.

Fused, as `Model/Program.lean` explains: the features here are already the
post-sum ones, because `blockTensor cP cQ` carries both the product stage `Ψ_S`
and the same-scope linear map `L_S` of main.tex:890–894. -/
def candidates {gPl gQl gPr gQr gP gQ : ℕ}
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ)
    {l : Region (Coord gPl gQl)} {r : Region (Coord gPr gQr)}
    (Rl : Reduction l) (Rr : Reduction r) :
    WPS (Rl.Idx × Rr.Idx) (Coord gP gQ) :=
  WPS.tensor (blockTensor cP cQ) Rl.core Rr.core

/-- **The index type one `Sparsify` call returns**: exactly `prior.size d_S` rows,
zero-padded (see decision 2 of `SparsifyPrior`'s docstring).  Static — it does not
depend on the draw — which is what lets the run's randomness be an ordinary
sequential product and lets claim (2) take `Fintype.card` of it. -/
abbrev RetainedIdx {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    (gP gQ : ℕ) : Type :=
  Fin (prior.size (Fintype.card (Coord gP gQ)))

/-! ### The bottom-up construction

The two defining equations of `built`, which are the recursion every statement
about `Reduction.Sparsifies`, `Reduction.core` and `maxInternalCard` inducts
along. -/

/-- **P1, main.tex:888.**  At a leaf region the construction is the exact weighted
assignment set: every `a ∈ Ω_i`, weight `1`, feature `Φ_{{i}}(a) = [θP · ; θQ · ]`.
No randomness, no error. -/
@[simp] theorem built_leaf {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ)
    (t : Program.Tape prior) :
    built prior (Circuit.leaf θP) (Circuit.leaf θQ) t
      = Reduction.leaf (Fin m) (fun a => Sum.elim (fun j => θP j a) (fun j => θQ j a)) :=
  rfl

/-- **P3, main.tex:896.**  At a product region the construction is the node whose
stored set is `Sparsify`'s output on the candidate Cartesian product of the two
children's, drawn at this region's own tape address `[]`.  Exactly one
sparsification per product region, and none between the product and sum stages. -/
@[simp] theorem built_node {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {Vl Vr : Vtree} {gPl gPr gP gQl gQr gQ : ℕ}
    (lP : Circuit Vl gPl) (rP : Circuit Vr gPr)
    (lQ : Circuit Vl gQl) (rQ : Circuit Vr gQr)
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ)
    (t : Program.Tape prior) :
    built prior (Circuit.node lP rP cP) (Circuit.node lQ rQ cQ) t
      = Reduction.node (blockTensor cP cQ)
          (built prior lP lQ (fun p => t (false :: p)))
          (built prior rP rQ (fun p => t (true :: p)))
          (RetainedIdx prior gP gQ)
          (prior.out
            (candidates cP cQ
              (built prior lP lQ (fun p => t (false :: p)))
              (built prior rP rQ (fun p => t (true :: p))))
            (t [])) :=
  rfl

/-! ### The tape and its law

`graft`'s three equations and `tapeLaw`'s two.  The analysis needs them to turn
`SparsifyPrior.bad_prob` — quantified over *every* candidate set — into the
conditional per-step bound the union bound of main.tex:926 consumes. -/

@[simp] theorem graft_nil {δ η' : ℝ} {prior : TvDomainReduction.SparsifyPrior δ η'}
    (x : prior.Draw) (tl tr : Program.Tape prior) : Run.graft x tl tr [] = x := rfl

@[simp] theorem graft_false {δ η' : ℝ} {prior : TvDomainReduction.SparsifyPrior δ η'}
    (x : prior.Draw) (tl tr : Program.Tape prior) (p : List Bool) :
    Run.graft x tl tr (false :: p) = tl p := rfl

@[simp] theorem graft_true {δ η' : ℝ} {prior : TvDomainReduction.SparsifyPrior δ η'}
    (x : prior.Draw) (tl tr : Program.Tape prior) (p : List Bool) :
    Run.graft x tl tr (true :: p) = tr p := rfl

/-- A leaf region consumes no randomness (main.tex:888). -/
@[simp] theorem tapeLaw_leaf {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ) :
    Run.tapeLaw prior (Circuit.leaf θP) (Circuit.leaf θQ)
      = PMF.pure (fun _ => prior.draw₀) :=
  rfl

/-- **The history-dependent step.**  The two children's tapes are drawn first;
`Program.build` is then run on them to recover the candidate set this region
actually sees; and only then is this region's draw taken from `prior.law` of that
set.  This is why an unconditional per-call failure bound would not compose. -/
@[simp] theorem tapeLaw_node {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η')
    {Vl Vr : Vtree} {gPl gPr gP gQl gQr gQ : ℕ}
    (lP : Circuit Vl gPl) (rP : Circuit Vr gPr)
    (lQ : Circuit Vl gQl) (rQ : Circuit Vr gQr)
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ) :
    Run.tapeLaw prior (Circuit.node lP rP cP) (Circuit.node lQ rQ cQ)
      = (Run.tapeLaw prior lP lQ >>= fun tl =>
          Run.tapeLaw prior rP rQ >>= fun tr =>
            prior.law (candidates cP cQ (built prior lP lQ tl) (built prior rP rQ tr))
              >>= fun x => PMF.pure (Run.graft x tl tr)) :=
  rfl

/-! ### The estimator and the root query -/

@[simp] theorem Dtilde_eq {V : Vtree} {gP gQ : ℕ} {C : CircuitPair V gP gQ}
    (R : CircuitPair.Reduction C) (jP : Fin gP) (jQ : Fin gQ) :
    TvDomainReduction.Dtilde R jP jQ = (1 / 2) * R.core.E (TvDomainReduction.aTV jP jQ) :=
  rfl

/-- `a_TV` is `+1` on the designated `P` root gate (main.tex:881). -/
@[simp] theorem aTV_inl {gP gQ : ℕ} (jP : Fin gP) (jQ : Fin gQ) (j : Fin gP) :
    TvDomainReduction.aTV jP jQ (Sum.inl j) = (if j = jP then (1 : ℝ) else 0) := rfl

/-- `a_TV` is `−1` on the designated `Q` root gate (main.tex:881). -/
@[simp] theorem aTV_inr {gP gQ : ℕ} (jP : Fin gP) (jQ : Fin gQ) (j : Fin gQ) :
    TvDomainReduction.aTV jP jQ (Sum.inr j) = (if j = jQ then (-1 : ℝ) else 0) := rfl

/-! ### The derived parameters (P0, main.tex:886) -/

@[simp] theorem perStepTol_eq (ε : ℝ) (L : ℕ) :
    TvDomainReduction.perStepTol ε L = ε / (3 * L) := rfl

@[simp] theorem perStepFail_eq (η : ℝ) (L : ℕ) :
    TvDomainReduction.perStepFail η L = η / L := rfl

/-! ### The static read-offs (P0, main.tex:871, 886, 906)

`q`, `W` and `|C|`, and the budget `M`, as recursions the resource claims induct
along. -/

@[simp] theorem leafDomMax_leaf (m : ℕ) : TvDomainReduction.leafDomMax (.leaf m) = m := rfl

@[simp] theorem leafDomMax_node (l r : Vtree) :
    TvDomainReduction.leafDomMax (.node l r)
      = max (TvDomainReduction.leafDomMax l) (TvDomainReduction.leafDomMax r) := rfl

@[simp] theorem gateWidth_leaf {m g : ℕ} (θ : Fin g → Fin m → ℝ) :
    TvDomainReduction.gateWidth (Circuit.leaf θ) = g := rfl

@[simp] theorem gateWidth_node {Vl Vr : Vtree} {gl gr g : ℕ}
    (l : Circuit Vl gl) (r : Circuit Vr gr) (c : Fin g → Fin gl → Fin gr → ℝ) :
    TvDomainReduction.gateWidth (Circuit.node l r c)
      = max g (max (TvDomainReduction.gateWidth l) (TvDomainReduction.gateWidth r)) := rfl

@[simp] theorem circuitSize_leaf {m g : ℕ} (θ : Fin g → Fin m → ℝ) :
    TvDomainReduction.circuitSize (Circuit.leaf θ) = g + g * m := rfl

@[simp] theorem circuitSize_node {Vl Vr : Vtree} {gl gr g : ℕ}
    (l : Circuit Vl gl) (r : Circuit Vr gr) (c : Fin g → Fin gl → Fin gr → ℝ) :
    TvDomainReduction.circuitSize (Circuit.node l r c)
      = g + g * gl * gr + TvDomainReduction.circuitSize l
          + TvDomainReduction.circuitSize r := rfl

@[simp] theorem pairWidth_eq {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) :
    TvDomainReduction.pairWidth C
      = max (TvDomainReduction.gateWidth C.P) (TvDomainReduction.gateWidth C.Q) := rfl

@[simp] theorem pairSize_eq {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) :
    TvDomainReduction.pairSize C
      = TvDomainReduction.circuitSize C.P + TvDomainReduction.circuitSize C.Q := rfl

@[simp] theorem pairRetainedBudget_eq {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ}
    (C : CircuitPair V gP gQ) (prior : TvDomainReduction.SparsifyPrior δ η') :
    TvDomainReduction.pairRetainedBudget C prior
      = TvDomainReduction.retainedBudget prior C.P C.Q := rfl

@[simp] theorem retainedBudget_leaf {δ η' : ℝ}
    (prior : TvDomainReduction.SparsifyPrior δ η') {m gP gQ : ℕ}
    (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ) :
    TvDomainReduction.retainedBudget prior (Circuit.leaf θP) (Circuit.leaf θQ) = 0 := rfl

@[simp] theorem retainedBudget_node {δ η' : ℝ}
    (prior : TvDomainReduction.SparsifyPrior δ η')
    {Vl Vr : Vtree} {gPl gPr gP gQl gQr gQ : ℕ}
    (lP : Circuit Vl gPl) (rP : Circuit Vr gPr)
    (lQ : Circuit Vl gQl) (rQ : Circuit Vr gQr)
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ) :
    TvDomainReduction.retainedBudget prior (Circuit.node lP rP cP) (Circuit.node lQ rQ cQ)
      = max (prior.size (gP + gQ))
          (max (TvDomainReduction.retainedBudget prior lP lQ)
            (TvDomainReduction.retainedBudget prior rP rQ)) := rfl

/-! ### The observed maximum (main.tex:905) -/

@[simp] theorem maxInternalCard_leaf {d : Type} (X : Type) [Fintype X] [DecidableEq X]
    (Φ : X → d → ℝ) : TvDomainReduction.maxInternalCard (Reduction.leaf X Φ) = 0 := rfl

@[simp] theorem maxInternalCard_node {dl dr d : Type} [Fintype dl] [Fintype dr]
    {l : Region dl} {r : Region dr} (M : d → dl → dr → ℝ)
    (Rl : Reduction l) (Rr : Reduction r) (ι : Type) [Fintype ι] (C : WPS ι d) :
    TvDomainReduction.maxInternalCard (Reduction.node M Rl Rr ι C)
      = max (Fintype.card ι)
          (max (TvDomainReduction.maxInternalCard Rl)
            (TvDomainReduction.maxInternalCard Rr)) := rfl

end TvDomainReduction.Interface
