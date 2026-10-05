import TvDomainReduction.Model.Program

/-!
# Where the randomness comes from

`Model/Program.lean` takes the `L` draws as an argument and computes.  This file
is the layer that says what law those draws have, and it is `noncomputable`
throughout because it mentions `PMF`.

## The one decision made here: the draws are *not* independent

The paper's union bound (main.tex:926) is over `L` sparsification steps whose
candidate matrices depend on earlier randomness: the matrix at a product region
is a function of the two children's realised coresets.  `thm:lewis_weights`
(main.tex:745) is stated for a *fixed* matrix, so an unconditional per-call bound
does not compose, and a product law over the `L` draws would be the wrong object.

`tapeLaw` is therefore a genuine **history-dependent sequential product**: at a
product region it first draws the two children's tapes, then *runs the program*
on them to find out what candidate set this region actually sees, and only then
draws this region's outcome from `prior.law` of that set.  That is how
`SparsifyPrior.bad_prob` — which is quantified over *every* candidate set — turns
into a conditional per-step bound that the union bound can use.

Note that the algorithm is called, not duplicated: the conditional law is
`prior.law` of `Program.build`'s own value, so there is one description of the
algorithm in this development and `Model/Run.lean` reads the history off it.

## The tape's shape, and why it has no length

`Program.Tape prior = List Bool → prior.Draw` addresses one draw per region by
its path in the shared v-tree.  There is no length to match against the input:
the addressing is injective by construction (distinct regions have distinct
paths) and the program reads exactly the `L` paths that are internal nodes of the
v-tree, ignoring the rest.  `tapeLaw` likewise only ever constrains those `L`
coordinates — `graft` writes this region's draw at `[]` and defers the two
children to `false :: ·` and `true :: ·` — so the law is supported on the
finitely many coordinates the program reads and `prior.draw₀` fills the leaves.
A counter-and-offset tape would have needed arithmetic on `Region.steps` in the
program and a matching offset proof here; a path has neither.

`graft` is written by recursion on the path rather than with a combinator, so each
of its three cases unfolds definitionally — which is what a bridge proof over the
tree inducts on.
-/

set_option autoImplicit false

namespace TvDomainReduction.Run

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations

/-- **One region's draw, grafted onto its two children's tapes.**

The region at the root of this subtree reads `[]`, the left child reads
`false :: ·` and the right child reads `true :: ·`.  Written by recursion on the
path, so all three equations hold by `rfl`. -/
def graft {δ η' : ℝ} {prior : TvDomainReduction.SparsifyPrior δ η'} (x : prior.Draw)
    (tl tr : Program.Tape prior) : Program.Tape prior
  | [] => x
  | false :: p => tl p
  | true :: p => tr p

/-- **The joint law of the run's `L` draws** — the history-dependent sequential
product described in the module docstring.

At a leaf no randomness is consumed, so the tape is the constant `prior.draw₀`.
At a product region the two children's tapes are drawn first; `Program.build` is
then run on each to recover the children's realised coresets; the candidate
Cartesian product `U_S = C_{S_h} × C_{S_ℓ}` is formed; and this region's draw
comes from `prior.law U_S`, i.e. from the law of a `Sparsify` call *on the matrix
this region actually sees*. -/
noncomputable def tapeLaw {δ η' : ℝ} (prior : TvDomainReduction.SparsifyPrior δ η') :
    {V : Vtree} → {gP gQ : ℕ} → Circuit V gP → Circuit V gQ → PMF (Program.Tape prior)
  | _, _, _, @Circuit.leaf _ _ _, @Circuit.leaf _ _ _ =>
      PMF.pure (fun _ => prior.draw₀)
  | _, _, _, @Circuit.node _ _ _ _ _ lP rP cP, @Circuit.node _ _ _ _ _ lQ rQ cQ => do
      let tl ← tapeLaw prior lP lQ
      let tr ← tapeLaw prior rP rQ
      let x ← prior.law (WPS.tensor (blockTensor cP cQ)
        (Program.build prior lP lQ tl).val.core (Program.build prior rP rQ tr).val.core)
      PMF.pure (graft x tl tr)

/-- **The algorithm, as a distribution over charged computations.**

`Charged.val <$> runLaw C prior` is what the run returns and
`Charged.steps Operations.rate` of a point of its support is what that run cost:
one object, three operators. -/
noncomputable def runLaw {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (prior : TvDomainReduction.SparsifyPrior δ η') :
    PMF (Comp (CircuitPair.Reduction C)) :=
  (tapeLaw prior C.P C.Q).map (fun t => Program.run C prior t)

/-- **The output distribution**: the law of the estimator `D̃` (main.tex:883).

This is the object claim (1) is a measure of. -/
noncomputable def answerLaw {δ η' : ℝ} {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (prior : TvDomainReduction.SparsifyPrior δ η') (jP : Fin gP) (jQ : Fin gQ) : PMF ℝ :=
  (runLaw C prior).map (fun p => TvDomainReduction.Dtilde p.val jP jQ)

/-! ## The same randomness, for Algorithm 1

`tapeLaw` is reused **unchanged** below: it is query-independent, and it is
already the history-dependent sequential product that Algorithm 1's union bound
needs — at step `t` it runs `Program.build` on the children's tapes to find the
candidate set `U_t = C_{t-1} × Ω_t` that this step actually sees, and only then
draws from `prior.law` of *that* set.  That is essential and not a convenience:
`U_t` is a deterministic function of `C_{t-1}`, hence of the first `t − 1` draws,
so the per-call bound `SparsifyPrior.bad_prob` has to be the conditional one
(quantified over *every* candidate set), which is what makes the paper's
one-sentence union bound (main.tex:843) sound.  Only the output wrapper differs,
so only `Program.runDense` replaces `Program.run`. -/

/-- **The algorithm of Theorem 1, as a distribution over charged computations**
(Algorithm 1, main.tex:763–784), on the instance compiled by
`Model/Prelude.mixPair`.

One draw per *internal* region of the caterpillar, i.e. `M.n − 1` of them — the
first coordinate's leaf coreset is exact (main.tex:888) — each with tolerance
`δ = ε/(3n)` and failure `η' = η/n` carried by the prior's indices. -/
noncomputable def runLawMix (M : TvDomainReduction.MixtureInstance) {δ η' : ℝ}
    (prior : TvDomainReduction.SparsifyPrior δ η') :
    PMF (Comp (CircuitPair.Reduction (TvDomainReduction.mixPair M))) :=
  (tapeLaw prior (TvDomainReduction.mixPair M).P (TvDomainReduction.mixPair M).Q).map
    (fun t => Program.runDense (TvDomainReduction.mixPair M) prior t)

/-- **The output distribution of Algorithm 1**: the law of
`D̃ = ½ E(C_n, w)` (main.tex:782).  This is the object the accuracy claim of
`thm:main_fptas` is a measure of. -/
noncomputable def answerLawMix (M : TvDomainReduction.MixtureInstance) {δ η' : ℝ}
    (prior : TvDomainReduction.SparsifyPrior δ η') : PMF ℝ :=
  (runLawMix M prior).map (fun p => TvDomainReduction.DtildeMix M p.val)

#modelClosure graft
#modelClosure tapeLaw
#modelClosure runLaw
#modelClosure answerLaw
#modelClosure runLawMix
#modelClosure answerLawMix

end TvDomainReduction.Run
