import TvDomainReduction.Model.Prior
import TvDomainReduction.Model.Run
import TvDomainReduction.Meta.ModelClosure
import TvDomainReduction.Analysis.CorrectnessProof
import TvDomainReduction.Analysis.SpaceProof
import TvDomainReduction.Analysis.TimeProof
import TvDomainReduction.Analysis.MixtureCorrectnessProof
import TvDomainReduction.Analysis.MixtureTimeProof
import TvDomainReduction.Analysis.WtaCorrectnessProof
import TvDomainReduction.Analysis.WtaTimeProof

/-!
# Theorem 4.1 — Probabilistic Circuit TV Approximation

`thm:pc_fpras`, main.tex:900–913, with its proof at main.tex:926–930 and its one
lemma (`lem:pc_invariant`) at main.tex:915–924.

> Given `ε, η ∈ (0,1)` and smooth, decomposable probabilistic circuits `C_P` and
> `C_Q` computing `P` and `Q`, structured with respect to a common v-tree, let
> `W`, `q` and `L ≥ 1` be as defined above.  The bottom-up coreset propagation
> outputs the estimator `D̃` satisfying
> `(1-ε) d_TV(P,Q) ≤ D̃ ≤ (1+ε) d_TV(P,Q)` with probability at least `1-η`.  Let
> `M` denote the maximum number of rows retained in any internal-region coreset,
> and let `|C| := |C_P| + |C_Q|`, where each circuit size counts its gates and
> wires.  The arithmetic running time is
> `Õ((q+M)|C| + L[W(q+M)² + W^ω])`, where
> `M = O(W L² log(2W) ε^{-2} log(L/η))`.

Three claims, three part theorems, one capstone:

* `pc_fpras_correct` — the accuracy claim.  **Can fail**, so it is a measure of
  `Run.answerLaw`, the output distribution of the single run.
* `pc_fpras_space` — the retained-size claim.  **Cannot fail**: it holds at every
  reachable outcome, and is stated that way, not as "with probability 1".
* `pc_fpras_time` — the arithmetic-running-time claim.  **Cannot fail**, likewise
  per-outcome.
* `pc_fpras` — the capstone, the conjunction the paper claims, proved from the
  three parts and nothing else.

## Where each hypothesis of the paper went

* **`ε, η ∈ (0,1)`** (main.tex:902) — binders `hε0`, `hε1`, `hη0`, `hη1`.
* **`L ≥ 1`** (main.tex:886, 902) — binder `hL : 0 < CircuitPair.steps C`.  The
  `L = 0` case, where "Sparsify is never called and the TV-distance can be
  computed deterministically and exactly" (main.tex:886), is an **explicit
  non-goal**: it is a different, deterministic algorithm and a different
  statement, and arlib's `relErr_of_calibrated` also needs `0 < steps`.
* **Smooth, decomposable, structured with respect to a common v-tree**
  (main.tex:862) — *not* Props.  They are discharged by the input **type**
  `CircuitPair V gP gQ`: a node's two children are circuits over the v-tree's two
  children (structuredness and decomposability), the sum layer at a region is a
  linear map of same-scope values (smoothness), and the *shared* index `V` is the
  common-v-tree hypothesis — two circuits over different v-trees cannot be paired
  at all.  A referee looking for these as hypotheses will not find them; this
  paragraph is where they went.
* **The two root gates output the normalised pmfs `P` and `Q`** (main.tex:862) —
  binders `hPnn`, `hPs`, `hQnn`, `hQs`, used to build the two `FinDist`s whose
  `tvDist` is `dTV`.
* **Nonnegative leaf tables and nonnegative sum weights** (main.tex:862) — **not
  assumed**.  The propagation argument never uses sign information: the
  invariant, the tensor composition and the linear-map step all hold for
  arbitrary real features, and the coresets' weights are nonnegative because the
  sampler says so (`WPS.wt_nonneg`), not because the circuit is.  The statement
  below is therefore slightly more general than the paper's literal
  "probabilistic circuit" class in this respect.
* **`δ ∈ (0,1/2)`** (main.tex:747) — *not* a hypothesis of this theorem.  It is
  `SparsifyPrior.hδ`, a field of the prior, discharged at the call site from
  `ε < 1` and `L ≥ 1` (which give `δ = ε/(3L) ≤ 1/3`).
* **Nondegeneracy of the candidate feature matrices** — *not* a hypothesis of
  this theorem, and deliberately absent from the binder list below.  `ℓ₁` Lewis
  weights need a nondegenerate Gram matrix and circuit feature matrices are
  routinely rank-deficient; `SparsifyPrior`'s `law`/`out`/`bad` are therefore
  total on candidate sets, so any instantiation must handle degeneracy itself.
  Pushing it onto the input circuit would be a far stronger and unverifiable
  assumption that the paper does not make.
* **`Sparsify` / `thm:lewis_weights`** (main.tex:745, 761) — binder
  `prior : SparsifyPrior (perStepTol ε L) (perStepFail η L)`.  The paper **cites**
  this result; so does this development.
* **`hprior : Prior`** — the development-wide assumption bundle, currently empty.

## Three places the Lean statement is not the paper's, and must not be mistaken for it

1. **`L` is larger than the paper's.**  `CircuitPair.steps C` is the number of
   internal v-tree nodes; the paper's `L` counts only *active* product regions
   (those where at least one circuit has a product gate, main.tex:886).  In
   arlib's encoding every internal node carries a product-then-sum layer, so a
   paper-inactive region is still counted and the Lean `L` is `≥` the paper's.
   Accuracy is unaffected (a larger `L` means a smaller `δ`, hence a stronger
   per-step requirement and the same `(1 ± ε)` conclusion); both **resource
   claims are weakened**, since `M` grows like `L²` and the time bound carries a
   factor `L`.  Everything below is the conservative version.

2. **`M` is the prior's static budget, and the paper's numeric bound on it is
   assumed through the prior.**  main.tex:905 both defines `M` as an observed
   maximum and asserts a bound on it; `pairRetainedBudget` is the budget,
   `maxInternalCard` is the observed maximum, and claim (2) is the pair of
   statements that the observed maximum never exceeds the budget and that the
   budget obeys the paper's formula.  The formula comes from
   `SparsifyPrior.size_le`, i.e. from `thm:lewis_weights`' claimed
   `O(d log d/δ² · log(1/η'))`.  **The only Lewis-weight sampler proved in this
   project's libraries (arlib's `lewis_importance_embeds`) calibrates to a
   strictly larger size than that cited optimum**, so a referee should read
   claim (2)'s numeric half as conditional on a prior that nothing in this
   project currently inhabits at the optimal size.  `log(2W)` appears as
   `Real.log (4 * W)`, because the sparsified matrix has `d_S ≤ 2W` columns and
   the paper's `log(2d)` is then `log(4W)`; base changes are absorbed into
   `SparsifyPrior.sizeConst`.

3. **The time bound is weaker than the paper's on the circuit-size term:
   `(q+M)²|C|` where the paper has `(q+M)|C|`.**  main.tex:894 applies the
   same-scope linear map `L_S` to the *surviving* rows only, which is what makes
   that term `O(M|C|)`; arlib's `Region.node` fuses product-then-sum into one
   bilinear tensor, so the program forms post-sum features on every candidate row
   and pays `N · wires(S)` with `N ≤ (q+M)²`.  The bracket `W(q+M)² + W^ω` is
   **not** affected — the sparsified matrix still has `d_S ≤ 2W` columns, so the
   Lewis call is still `Õ(W(q+M)² + W^ω)`.  This is a model gap, not a proof
   convenience: closing it needs a `Ψ`-stage in arlib's region tree.  See
   `Model/Program.lean`.

## This file now states two of the paper's theorems

Everything above and below about `pc_fpras` is `thm:pc_fpras` (main.tex:900), the
**circuit** theorem.  At the end of the file there is a second, independent
result: `thm:main_fptas` (main.tex:788–795), the paper's **mixture-of-products**
theorem, as `mixture_fpras_correct`, `mixture_fpras_time` and the capstone
`mixture_fpras`.  Neither supersedes the other — see the docstring of
`mixture_fpras` for exactly what the two share and the three ways they differ.

`Õ` itself is not formalised as asymptotic notation: a single-instance claim needs
explicit constants, and the paper gives none.  The suppressed constant of the
propagation is one existential `c`, and the suppressed constant and polylog of
the cited solver are `SparsifyPrior.costConst` and `SparsifyPrior.polylog`.  `ω`
appears only as `SparsifyPrior.mmExp`, with `2 ≤ ω ≤ 2.4` as a field — it is an
external constant about matrix multiplication, not a price this development sets.
-/

set_option autoImplicit false

namespace TvDomainReduction

open Arlib.Approximation
open Arlib.Computation
open Arlib.KnowledgeCompilation.Probabilistic
open TvDomainReduction.Model.Operations

/-! ## Claim (1): accuracy — can fail -/

/-- **`(1-ε) d_TV(P,Q) ≤ D̃ ≤ (1+ε) d_TV(P,Q)` with probability at least `1-η`**
(main.tex:902).

A measure of `Run.answerLaw C prior jP jQ`, the output distribution of the single
run `Run.runLaw C prior`: the probability that the estimator lands in the window
`Arlib.relErr ε (d_TV(P,Q))` is at least `1 - η`.  Nothing is claimed off that
event — the algorithm still returns a number there, and the paper says nothing
about it either.

The mechanism (main.tex:926–927): conditionally on all `L` sparsifications
succeeding, arlib's `Reduction.embeds_exact` — which **is** Lemma
`lem:pc_invariant` and is already proved, so it must not be restated — gives the
root coreset the window `(1 ± δ)^L` on every linear test; at `a_TV` the exact side
is `2 d_TV(P,Q)` (`dTV_eq_half_exactWPS_E`) and the coreset side is `2 D̃`; and
`δ = ε/(3L)` turns `(1 ± δ)^L` into `(1 ± ε)`
(`Reduction.relErr_of_calibrated`).  The union bound over the `L` steps costs
`L · η' = η`, and because each step's candidate matrix depends on earlier draws it
has to be the *conditional* form: `SparsifyPrior.bad_prob` is quantified over
every candidate set, and `Run.tapeLaw` is a history-dependent sequential
product. -/
theorem pc_fpras_correct (hprior : Prior)
    {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) (jP : Fin gP) (jQ : Fin gQ)
    (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x jP) (hPs : ∑ x : C.Assign, C.valP x jP = 1)
    (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x jQ) (hQs : ∑ x : C.Assign, C.valQ x jQ = 1)
    (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < CircuitPair.steps C)
    (prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
      (perStepFail η (CircuitPair.steps C))) :
    1 - ENNReal.ofReal η
      ≤ (Run.answerLaw C prior jP jQ).toOuterMeasure
          (Arlib.relErr ε (dTV C jP jQ hPnn hPs hQnn hQs)) := by
    exact TvDomainReduction.Analysis.pc_fpras_correct_proof hprior (V := V) (gP := gP) (gQ := gQ) C jP jQ hPnn hPs hQnn hQs ε η hε0 hε1 hη0 hη1 hL prior

/-! ## Claim (2): the retained sizes — cannot fail -/

/-- **Every internal-region coreset retains at most `M` rows, and
`M = O(W L² log(2W) ε^{-2} log(L/η))`** (main.tex:905–912, 929).

Two conjuncts, both unconditional — `thm:lewis_weights` bounds the number of
nonzero entries of its sampling matrix on *every* outcome, so this is a claim
about every reachable run and is stated that way rather than as "with probability
one":

* the observed maximum `maxInternalCard` of a run never exceeds the static budget
  `pairRetainedBudget C prior`, which is `prior.size` maximised over the internal
  regions;
* that budget obeys the paper's formula, with `log(2W)` appearing as
  `log(4W)` because `d_S ≤ 2W` (see the module docstring), and with
  `18 = 2 · 9` the `2` from `d_S ≤ 2W` and the `9` from `δ^{-2} = 9L²/ε²`.

Claim (3) is stated with *this* `M`, so the two resource claims are about the
same object. -/
theorem pc_fpras_space (hprior : Prior)
    {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < CircuitPair.steps C)
    (prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
      (perStepFail η (CircuitPair.steps C))) :
    (∀ p ∈ (Run.runLaw C prior).support,
        maxInternalCard (Charged.val p) ≤ pairRetainedBudget C prior)
      ∧ (pairRetainedBudget C prior : ℝ)
          ≤ prior.sizeConst * 18 * (pairWidth C : ℝ) * (CircuitPair.steps C : ℝ) ^ 2
              * Real.log (4 * pairWidth C)
              * Real.log (CircuitPair.steps C / η) / ε ^ 2 := by
    exact TvDomainReduction.Analysis.pc_fpras_space_proof hprior (V := V) (gP := gP) (gQ := gQ) C ε η hε0 hε1 hη0 hη1 hL prior

/-! ## Claim (3): the arithmetic running time — cannot fail -/

/-- **The run performs `Õ((q+M)²|C| + L[W(q+M)² + W^ω])` arithmetic operations.**

main.tex:904–912 and the accounting at main.tex:929, with the circuit-size term
weakened from `(q+M)|C|` to `(q+M)²|C|`; see point 3 of the module docstring, and
`Model/Program.lean` for why the fused product-then-sum node forces it.

Per-outcome over the support of `Run.runLaw`, because it cannot fail.  The
accounting, region by region:

* each child domain has at most `q` rows if it is a leaf and at most `M`
  otherwise, so every binary product region has `|U_S| ≤ (q+M)²` candidate rows;
* forming the fused features on those rows costs `O((q+M)² · wires(S))`, and the
  wires sum to `|C|` over the run — the `(q+M)²|C|` term, which also absorbs the
  `O(q|C|)` leaf-table evaluations and the `O(M)` root evaluation (`a_TV` has one
  `+1` and one `−1`, so each root inner product is a single subtraction);
* the sparsified matrix has `d_S ≤ 2W` columns, so one Lewis-weight call costs
  `prior.callCost ((q+M)²) (2W) ≤ Õ(W(q+M)² + W^ω)` by
  `SparsifyPrior.callCost_le` — the bracket, paid `L` times.

`c` is the propagation's own suppressed constant, quantified once; the solver's
constant and polylog are the prior's fields, and `ω` is `prior.mmExp`.

Two pieces of slack in the first term are deliberate and needed for a
*single-instance* claim, which is what `Õ` does not give.  `pairSize C + steps C`
rather than `pairSize C`: a region whose two circuits both have zero gates there
contributes `1` to `L` and `0` to `|C|`, so `L ≤ |C|` is not a theorem, and it is
not worth a hypothesis.  `1 +`: a run on a circuit with an empty leaf domain
still performs the final division, and `(q+M)² = 0` there.  Neither affects the
asymptotics the paper states. -/
theorem pc_fpras_time (hprior : Prior)
    {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < CircuitPair.steps C)
    (prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
      (perStepFail η (CircuitPair.steps C))) :
    ∃ c : ℕ, ∀ p ∈ (Run.runLaw C prior).support,
      (Charged.steps rate p : ℝ)
        ≤ c * (1 + ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
                    * (pairSize C + CircuitPair.steps C))
          + (CircuitPair.steps C : ℝ) * prior.costConst
              * prior.polylog
                  (2 * pairWidth C * (leafDomMax V + pairRetainedBudget C prior) ^ 2)
              * (2 * (pairWidth C : ℝ)
                    * ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
                  + (2 * pairWidth C : ℝ) ^ prior.mmExp) := by
    exact TvDomainReduction.Analysis.pc_fpras_time_proof hprior (V := V) (gP := gP) (gQ := gQ) C ε η hε0 hε1 hη0 hη1 hL prior

/-! ## The author's result -/

/-- **Theorem 4.1 (Probabilistic Circuit TV Approximation)**, `thm:pc_fpras`,
main.tex:900–913.

The conjunction the paper claims, about one run of the bottom-up coreset
propagation `Run.runLaw C prior`: the estimator is a `(1 ± ε)` relative
approximation of `d_TV(P,Q)` except on an event of probability at most `η`; every
internal-region coreset retains at most `M` rows and `M` obeys the stated bound;
and the run performs the stated number of arithmetic operations.

Read the module docstring before reading this statement: the Lean `L`, the Lean
`M` and the Lean time bound are each stated here in a form that differs from the
paper's, in each case conservatively, and in each case for a reason recorded
there.  The `L = 0` case is an explicit non-goal. -/
theorem pc_fpras (hprior : Prior)
    {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) (jP : Fin gP) (jQ : Fin gQ)
    (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x jP) (hPs : ∑ x : C.Assign, C.valP x jP = 1)
    (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x jQ) (hQs : ∑ x : C.Assign, C.valQ x jQ = 1)
    (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < CircuitPair.steps C)
    (prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
      (perStepFail η (CircuitPair.steps C))) :
    -- (1) accuracy, with probability at least `1 - η`
    (1 - ENNReal.ofReal η
        ≤ (Run.answerLaw C prior jP jQ).toOuterMeasure
            (Arlib.relErr ε (dTV C jP jQ hPnn hPs hQnn hQs)))
    -- (2) the retained sizes, on every reachable outcome
    ∧ ((∀ p ∈ (Run.runLaw C prior).support,
          maxInternalCard (Charged.val p) ≤ pairRetainedBudget C prior)
        ∧ (pairRetainedBudget C prior : ℝ)
            ≤ prior.sizeConst * 18 * (pairWidth C : ℝ) * (CircuitPair.steps C : ℝ) ^ 2
                * Real.log (4 * pairWidth C)
                * Real.log (CircuitPair.steps C / η) / ε ^ 2)
    -- (3) the arithmetic running time, on every reachable outcome
    ∧ (∃ c : ℕ, ∀ p ∈ (Run.runLaw C prior).support,
        (Charged.steps rate p : ℝ)
          ≤ c * (1 + ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
                      * (pairSize C + CircuitPair.steps C))
            + (CircuitPair.steps C : ℝ) * prior.costConst
                * prior.polylog
                    (2 * pairWidth C * (leafDomMax V + pairRetainedBudget C prior) ^ 2)
                * (2 * (pairWidth C : ℝ)
                      * ((leafDomMax V : ℝ) + pairRetainedBudget C prior) ^ 2
                    + (2 * pairWidth C : ℝ) ^ prior.mmExp)) :=
  ⟨pc_fpras_correct hprior C jP jQ hPnn hPs hQnn hQs ε η hε0 hε1 hη0 hη1 hL prior,
   pc_fpras_space hprior C ε η hε0 hε1 hη0 hη1 hL prior,
   pc_fpras_time hprior C ε η hε0 hε1 hη0 hη1 hL prior⟩

/-! # Theorem 1 — Mixtures of Product Distributions

`thm:main_fptas`, main.tex:788–795 ("Correctness and Complexity"), with its
proofs at main.tex:842–848 (correctness) and main.tex:850–857 (complexity), its
two lemmas `lem:one_step` (main.tex:802–811) and `lem:propagation`
(main.tex:823–840), its algorithm `alg:fptas` (main.tex:763–784), its setting at
main.tex:712–733 and its subroutine `thm:lewis_weights` (main.tex:745–752).

> Given `ε, η ∈ (0,1)`, Algorithm 1 outputs a value `D̃` such that
> `(1 − ε) d_TV(P,Q) ≤ D̃ ≤ (1 + ε) d_TV(P,Q)` with probability at least `1 − η`.
> The algorithm runs in time polynomial in `n, k, 1/ε, log(1/η)`, and the maximum
> domain size `max_t |Ω_t|`.

Two claims, two part theorems, one capstone:

* `mixture_fpras_correct` — the accuracy claim.  **Can fail**, so it is a measure
  of `Run.answerLawMix`, the output distribution of the single run.  Nothing is
  claimed on the complementary event, and the paper claims nothing there either.
* `mixture_fpras_time` — the arithmetic-running-time claim.  **Cannot fail**: the
  retained index types are static (the prior returns exactly `size d` rows,
  zero-padded) and `prior.callCost` depends only on `(N, d)`, so every outcome in
  the support has the same tally.  Stated per-outcome, not as "with probability
  one"; the paper states no probability qualifier either.
* `mixture_fpras` — the capstone, the conjunction the paper claims, proved from
  the two parts and nothing else.

Unlike `thm:pc_fpras` this theorem makes **no separate claim about the retained
coreset size**: `m` is an algorithm parameter (Algorithm 1 line 2) that feeds the
time bound, not a conclusion.  So there is no `mixture_fpras_space`.
-/

/-! ## Claim (1): accuracy — can fail -/

/-- **`(1 − ε) d_TV(P,Q) ≤ D̃ ≤ (1 + ε) d_TV(P,Q)` with probability at least
`1 − η`** (main.tex:790–794), for `P` and `Q` the two mixtures of product
distributions given by `M`.

A measure of `Run.answerLawMix M prior`, the output distribution of the single
run `Run.runLawMix M prior`: the probability that the estimator
`DtildeMix = ½ E(C_n, w)` lands in the window `Arlib.relErr ε (d_TV(P,Q))` is at
least `1 − η`.

The mechanism (main.tex:842–848), and where each step of the paper's proof went:

* `lem:one_step` (main.tex:802–811) is `SparsifyPrior.embeds_of_not_bad`;
* the union bound over the steps (main.tex:843) is
  `Analysis.reduceLaw_not_sparsifies_le`, already proved and query-independent;
* `lem:propagation` (main.tex:823–840) — the hybrid functional `F_t`, the future
  multiplier `S_{>t}` and the telescoping — is **not formalised at all**.  Its
  content is one node of arlib's `Reduction.embeds_exact`, which quantifies over
  *all* queries at *every* region and is therefore strictly stronger than the
  paper's fixed-future functional; it is already proved and must not be
  restated.  The telescoped window `(1 ± δ)^n` is that invariant's exponent.
* the calibration `(1 + ε/3n)^n ≤ e^{ε/3} ≤ 1 + ε` and `(1 − ε/3n)^n ≥ 1 − ε`
  (main.tex:845–847) is `Reduction.relErr_of_calibrated`;
* `F_0 = d_TV(P,Q)` (main.tex:821) is the mixture analogue of
  `dTV_eq_half_exactWPS_E`, namely
  `½ · (mixPair M).toRegion.exactWPS.E (wVec M) = dTVmix M …`, whose content is
  the pointwise identity `⟨w, R(x)⟩ = P(x) − Q(x)` (main.tex:730).  That is where
  the signs of `wVec` are used, and it is an `Analysis/` obligation;
* `F_n = D̃` is `DtildeMix` by definition.

Because each step's candidate matrix `U_t = C_{t−1} × Ω_t` depends on the earlier
draws, the per-step failure bound has to be the **conditional** one:
`SparsifyPrior.bad_prob` is quantified over every candidate set and
`Run.tapeLaw` is a history-dependent sequential product.  The paper's
one-sentence union bound is sound only under this reading, which it does not
state. -/
theorem mixture_fpras_correct (hprior : Prior)
    (M : MixtureInstance) (hM : M.IsStochastic)
    (hPnn : ∀ x, 0 ≤ mixPmfP M x) (hPs : ∑ x, mixPmfP M x = 1)
    (hQnn : ∀ x, 0 ≤ mixPmfQ M x) (hQs : ∑ x, mixPmfQ M x = 1)
    (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hn : 2 ≤ M.n)
    (prior : SparsifyPrior (perStepTol ε M.n) (perStepFail η M.n)) :
    1 - ENNReal.ofReal η
      ≤ (Run.answerLawMix M prior).toOuterMeasure
          (Arlib.relErr ε (dTVmix M hPnn hPs hQnn hQs)) := by
    exact TvDomainReduction.Analysis.mixture_fpras_correct_proof hprior M hM hPnn hPs hQnn hQs ε η hε0 hε1 hη0 hη1 hn prior

/-! ## Claim (2): the arithmetic running time — cannot fail -/

/-- **The run performs a number of arithmetic operations bounded by a single
polynomial in `n`, `k`, `1/ε`, `log(1/η)` and `q = max_t |Ω_t|`**
(main.tex:794, with the accounting at main.tex:850–857).

The constants `c` and `D` are quantified **before every instance binder** and
depend only on the cited Lewis-weight solver's suppressed constants, which is
what "polynomial in …" means and what `SparsifyFamily` is for.  An existential
constant quantified *after* the instance would be vacuous for a run whose
operation count is a fixed number — precisely the defect the handoff notes at the
bottom of this file record about `pc_fpras_time`, and the reason this theorem is
not stated in that shape.

The bound is written as a monomial in the five quantities the paper names.  That
is exactly as strong as a general polynomial bound because each factor is `≥ 1`
under the hypotheses (`M.n ≥ 2` by binder; `M.k ≥ 1` and `M.q ≥ 1` derived from
`hM`, since a pmf cannot live on an empty domain and weights cannot sum to `1`
over an empty index; `1/ε > 1` from `ε < 1`; `1 + log(1/η) ≥ 1` from `η < 1`), so
any monomial in them is dominated by a single power of their product.

Per-outcome over the support of `Run.runLawMix`, because it cannot fail.

**What this does and does not certify.**  The claim is in the arithmetic
(real-RAM) model, counted in the `ArithOp` currency of `Model/Operations.lean`,
exactly as main.tex:856 states it; it is **not** an FPRAS in the usual
bit-complexity sense, and no bit-size analysis of the Lewis-weight computation is
attempted here or in the paper.  And it certifies only the headline
"polynomial": the paper's **explicit** per-step figure
`Õ(|Ω_t| n² k² ε^{-2} log(n/η) + k^ω)` (main.tex:851–855) is an **explicit
non-goal**, because `Program.build` evaluates each node through arlib's generic
dense coefficient tensor (`k₁³ + k₂³` entries, so `O(k³)` per candidate row)
rather than exploiting the diagonal structure (`O(k)` per row) that the paper's
accounting assumes.  The Lean bound is therefore about a factor `k²` worse than
main.tex:853–855 and must not be advertised as matching it. -/
theorem mixture_fpras_time (hprior : Prior) (fam : SparsifyFamily) :
    ∃ c D : ℕ, ∀ (M : MixtureInstance), M.IsStochastic → ∀ (ε η : ℝ),
      0 < ε → ε < 1 → 0 < η → η < 1 → 2 ≤ M.n →
      ∀ prior : SparsifyPrior (perStepTol ε M.n) (perStepFail η M.n),
        fam.Member prior →
        ∀ p ∈ (Run.runLawMix M prior).support,
          (Charged.steps rate p : ℝ)
            ≤ (c : ℝ) * ((M.n : ℝ) * (M.k : ℝ) * (M.q : ℝ) * (1 / ε)
                          * (1 + Real.log (1 / η))) ^ D := by
    exact TvDomainReduction.Analysis.mixture_fpras_time_proof hprior fam

/-! ## The author's first result -/

/-- **Theorem 1 (Correctness and Complexity)**, `thm:main_fptas`,
main.tex:788–795.

The conjunction the paper claims, about one run of Algorithm 1
(`Run.runLawMix M prior`, main.tex:763–784) on the two mixtures of product
distributions given by `M`: the estimator `D̃ = ½ E(C_n, w)` is a `(1 ± ε)`
relative approximation of `d_TV(P,Q)` except on an event of probability at most
`η`; and the run performs a number of arithmetic operations bounded by one
polynomial in `n`, `k`, `1/ε`, `log(1/η)` and `q`, uniformly over instances and
over `(ε, η)`.

## This is *not* `pc_fpras`, and neither supersedes the other

`pc_fpras` (above) is `thm:pc_fpras`, the probabilistic-circuit theorem, and is
already proved.  This theorem is stated separately rather than derived from it,
because all three of `pc_fpras`'s conjuncts are phrased in vocabulary that does
not fit here.  What is **shared** is everything below the query layer, and that
is most of the work: `Program.build`, `Run.tapeLaw`,
`Analysis.reduceLaw_not_sparsifies_le`, `Reduction.embeds_exact`,
`Reduction.relErr_of_calibrated`, `retainedBudget`, `perStepTol`, `perStepFail`
and `SparsifyPrior`, all reused unchanged.  What **differs** is exactly three
things:

1. **The root query is the dense `w = (+α, −β)`, not `a_TV`.**  `a_TV` is `+1` on
   one designated `P` root gate and `−1` on one designated `Q` root gate; the
   compiled mixture pair's root gates are the `k₁ + k₂` individual *components*,
   and Algorithm 1 line 13 queries them all at once.  Reusing `a_TV` here would
   compute the distance between two individual components.  Hence `wVec`,
   `DtildeAt` (which generalises `Dtilde`'s query slot — `Dtilde R jP jQ =
   DtildeAt R (aTV jP jQ)` by `rfl`) and `Program.runDense`, whose root charge is
   the dense one (`k` multiplications and `k − 1` additions per retained row)
   rather than `Program.run`'s single subtraction.
2. **The distance is a mixture distance, not a root-gate distance.**  `dTVmix` is
   the library's `FinDist.tvDist` between `Pmix` and `Qmix`, whose pmfs are the
   paper's `∑_i α_i ∏_t P_{i,t}(x_t)` written out as `mixPmfP` / `mixPmfQ`.  The
   settled `dTV` is the distance between two designated root gates and is the
   wrong object here.
3. **The time claim is uniform.**  `c` and `D` are quantified before all instance
   binders, against a `SparsifyFamily` whose constants are shared across every
   `(δ, η')` the run instantiates.

## Where each hypothesis of the paper went

* **`ε, η ∈ (0,1)`** (main.tex:790) — binders `hε0`, `hε1`, `hη0`, `hη1`.
  Algorithm 1's REQUIRE line (main.tex:767) says only `η > 0`; the **theorem**
  governs, and `η ≥ 1` would make the conclusion empty.
* **`P` and `Q` are mixtures of `k₁` and `k₂` product distributions with weights
  `α`, `β` and marginals `P_{i,t}`, `Q_{i,t}`** (main.tex:713–716) — the input
  **type** `MixtureInstance` together with `mixPmfP` / `mixPmfQ`, which are the
  paper's formulas written out.  Without the product form there is no Hadamard
  feature recursion and no algorithm.
* **`α, β ≥ 0` summing to `1`, every marginal a pmf** (main.tex:713–716) — binder
  `hM : M.IsStochastic`.  It is used for exactly one thing: making the estimated
  quantity a total variation distance between genuine distributions.  The
  `(1 ± ε)` window argument uses no sign information, the same finding already
  recorded for the circuit case.
* **`∑_x P(x) = 1` and `∑_x Q(x) = 1`** — binders `hPnn`, `hPs`, `hQnn`, `hQs`,
  which build the two `FinDist`s whose `tvDist` is `dTVmix`.  These are
  **consequences of `hM`**, not extra assumptions: `hPnn` is immediate, and
  `hPs` is the product-space factorisation
  `∑_x ∏_t f_t(x_t) = ∏_t ∑_a f_t(a)` applied to each component.  They appear as
  binders only because a `FinDist` field needs the proof term and `Model/` holds
  no proofs; deriving them is an `Analysis/` obligation, after which they become
  removable.  A referee should read the hypothesis set as the paper's.
* **`n ≥ 1`** (main.tex:713, implicit in `δ = ε/(3n)`) — strengthened to
  `hn : 2 ≤ M.n`.  `(mixPair M).steps = M.n − 1`, and
  `Reduction.relErr_of_calibrated` needs `0 < steps`.  **`M.n = 1` is an explicit
  non-goal**: it is the paper's own `L = 0` case (main.tex:886), where "Sparsify
  is never called and the TV-distance can be computed deterministically and
  exactly" — a different, deterministic algorithm and a different statement.
* **Every `Ω_t` nonempty, and `k₁, k₂ ≥ 1`** — *not* binders.  Both follow from
  `hM` (a pmf cannot live on an empty domain; weights cannot sum to `1` over an
  empty index) and both are needed, for the sampler's `Nonempty` requirement and
  so that every factor of the time monomial is `≥ 1`.  Derived, not assumed.
* **`δ ∈ (0,1/2)`** (main.tex:747) — *not* a hypothesis.  It is
  `SparsifyPrior.hδ`, a field of the prior, discharged at the call site from
  `ε < 1` and `M.n ≥ 2` (which give `δ = ε/(3 M.n) ≤ 1/6`).
* **Nondegeneracy of the candidate feature matrices** — *not* a hypothesis, and
  deliberately absent from the binder list.  This is more acute here than in the
  circuit case: a mixture feature is a **product** of marginals, so a zero row
  arises whenever a prefix has zero probability under every component, and
  duplicated or proportional components give rank-deficient matrices.  The
  paper states no such hypothesis and it is false for generic mixtures;
  `SparsifyPrior`'s `law`/`out`/`bad` are therefore total on candidate sets, and
  any instantiation must handle degeneracy itself.  It must never migrate onto
  `MixtureInstance`.
* **`Sparsify` / `thm:lewis_weights`** (main.tex:745, 761) — binder
  `prior : SparsifyPrior (perStepTol ε M.n) (perStepFail η M.n)`, and for the
  uniform time claim additionally `fam : SparsifyFamily` with
  `fam.Member prior`.  The paper **cites** this result; so does this
  development, and **nothing in this project's libraries inhabits it at the
  cited optimal size** — arlib's `lewis_importance_embeds` calibrates to a
  strictly larger one.  Since `m` feeds the time bound here, claim (2) inherits
  that conditionality.
* **`hprior : Prior`** — the development-wide assumption bundle, still empty.
  `Prior` is **not** widened for this theorem: the uniformity assumption it needs
  is the new, theorem-specific `SparsifyFamily` in `Model/Prior.lean`.

## Three further places the Lean statement is not the paper's

1. **The run performs `M.n − 1` sparsifications, not `M.n`, while keeping
   `δ = ε/(3 M.n)` and `η' = η/M.n`.**  Algorithm 1 line 12 at `t = 1`
   sparsifies `U_1 = C_0 × Ω_1`, which is just the exact leaf set of `Ω_1`;
   §4.2's "Leaf Gates" paragraph (main.tex:888) keeps leaf coresets exact, and so
   do `Program.build` and `Reduction.leaf`.  **The paper is internally
   inconsistent here**, and this development follows §4.2.  The slack is entirely
   in the safe direction: a smaller per-step tolerance than `ε/(3·steps)` and one
   fewer failure event, with `(M.n − 1)·η/M.n ≤ η`.  It is also why the accuracy
   proof needs a `Reduction.Sparsifies` monotonicity step, which arlib does not
   have — a pure proof-side obligation, deliberately not in this surface.
2. **The circuit case's fused product-then-sum model gap is vacuous here.**  Every
   internal node of `mixPair` carries a *diagonal* tensor, so there is no sum
   layer, `Ψ_S = Φ_S`, and the paper's "apply `L_S` to the surviving rows only"
   step does not exist.  A reader arriving from point 3 of this module's first
   docstring should not look for it.
3. **`Algorithm 1` line 2's `m = Θ(…)` is read as an upper bound only.**  Nothing
   downstream uses the matching lower bound, and `SparsifyPrior` records only
   `size_le`.  The label `thm:main_fptas` says "fptas"; the result is randomised,
   and the algorithm's caption and main.tex:856 both correctly call it an FPRAS.
   This docstring uses FPRAS. -/
theorem mixture_fpras (hprior : Prior) (fam : SparsifyFamily) :
    -- (1) accuracy, with probability at least `1 - η`
    (∀ (M : MixtureInstance), M.IsStochastic →
        ∀ (hPnn : ∀ x, 0 ≤ mixPmfP M x) (hPs : ∑ x, mixPmfP M x = 1)
          (hQnn : ∀ x, 0 ≤ mixPmfQ M x) (hQs : ∑ x, mixPmfQ M x = 1) (ε η : ℝ),
          0 < ε → ε < 1 → 0 < η → η < 1 → 2 ≤ M.n →
        ∀ prior : SparsifyPrior (perStepTol ε M.n) (perStepFail η M.n),
          1 - ENNReal.ofReal η
            ≤ (Run.answerLawMix M prior).toOuterMeasure
                (Arlib.relErr ε (dTVmix M hPnn hPs hQnn hQs)))
    -- (2) the arithmetic running time, on every reachable outcome, with constants
    --     fixed before the instance
    ∧ (∃ c D : ℕ, ∀ (M : MixtureInstance), M.IsStochastic → ∀ (ε η : ℝ),
        0 < ε → ε < 1 → 0 < η → η < 1 → 2 ≤ M.n →
        ∀ prior : SparsifyPrior (perStepTol ε M.n) (perStepFail η M.n),
          fam.Member prior →
          ∀ p ∈ (Run.runLawMix M prior).support,
            (Charged.steps rate p : ℝ)
              ≤ (c : ℝ) * ((M.n : ℝ) * (M.k : ℝ) * (M.q : ℝ) * (1 / ε)
                            * (1 + Real.log (1 / η))) ^ D) :=
  ⟨fun M hM hPnn hPs hQnn hQs ε η hε0 hε1 hη0 hη1 hn prior =>
      mixture_fpras_correct hprior M hM hPnn hPs hQnn hQs ε η hε0 hε1 hη0 hη1 hn prior,
   mixture_fpras_time hprior fam⟩

/-! # Theorem 5.1 — Weighted Tree Automata

`thm:wta_fpras`, main.tex:996–1003, with its proof at main.tex:1005–1035 and its
setting at main.tex:943–992 (§5).

> Given `ε, η ∈ (0,1)`, two distributions `P` and `Q` induced by two nonnegative
> weighted tree automata on the same tree `T`, there exists an FPRAS that outputs
> a real number `d̂` such that `(1−ε) d_TV(P,Q) ≤ d̂ ≤ (1+ε) d_TV(P,Q)`, with
> probability at least `1−η` in time
> `Õ(|V| d² (q + d + d²|V|²/ε² · log(|V|/η))² + |V| d^{2ω})`, where
> `q := max_i |Ω_i|` and `d := max_u d_u` are the maximum leaf-domain size and
> joint node-interface dimension.

Two claims, two part theorems, one capstone:

* `wta_fpras_correct` — the accuracy claim.  **Can fail**, so it is a measure of
  `Run.answerLawWTA`, the output distribution of the single run.
* `wta_fpras_time` — the arithmetic-running-time claim.  **Cannot fail**: the
  retained index types are static and `prior.callCost` depends only on `(N, d)`,
  so it is stated per outcome over the support of `Run.runLawWTA`.
* `wta_fpras` — the capstone, proved from the two parts and nothing else.

As for `thm:main_fptas`, the paper makes no separate retained-size claim here: `M`
appears only inside the time bound.  "There exists an FPRAS" is witnessed by the
specific algorithm `Program.runWTA`, which is stronger, and "time" is the
arithmetic (real-RAM) operation count of `Model/Operations.lean` (main.tex:751,
856); no bit-complexity claim is made.

## This is *not* derived from `pc_fpras`

The engine is shared and reused unchanged — `Program.build`, `Program.runDense`,
`Run.tapeLaw`, `Analysis.reduceLaw_not_sparsifies_le`, `Reduction.embeds_exact`
(= `lem:pc_invariant`), `Reduction.relErr_of_calibrated`, `DtildeAt`,
`perStepTol`, `perStepFail`, `retainedBudget`, `SparsifyPrior`, `SparsifyFamily`.
But `pc_fpras`'s statement does not fit a WTA: its query `aTV` is `±1`, and its
distance `dTV` / `rootDistP` requires the **root gate itself** to sum to `1`,
which is false for an automaton's unnormalised weight `f_R` (`Z_R ≠ 1` in
general).  And `pc_fpras_time` has the vacuous `∃ c`-after-the-instance shape
recorded in the handoff notes below.  So the WTA theorem is stated separately, in
the new vocabulary `aWTA = (Z_P^{-1}, −Z_Q^{-1})`, `wtaDistP` / `wtaDistQ`
(`f_R/Z_R`), `dTVwta`, `DtildeWTA` of `Model/Prelude.lean`.  Its cross-check —
`½ · C.toRegion.exactWPS.E (aWTA C) = dTVwta C …`, i.e. eq:wta-pointwise-difference
(main.tex:986–991), via the DP identity `circuitMass C.P 0 = wtaZP C`
(main.tex:967) — is an `Analysis/` obligation and the place the signs and
inverses of `aWTA` are used.

## Where each hypothesis of the paper went

* **`ε, η ∈ (0,1)`** (main.tex:997) — binders `hε0`, `hε1`, `hη0`, `hη1`.
* **`P`, `Q` induced by two WTAs on the same tree, root dimension `1`**
  (main.tex:943–962) — the input **type** `C : CircuitPair V 1 1`.  The shared
  `V` is "the same tree"; `gP = gQ = 1` is `d_r^R = 1`; the node tensor's index
  order (output, left, right) is main.tex:953 through `CircuitPair.valP_node`.
  The paper's zero-padding (main.tex:1006) and scalar product/sum-gate expansion
  (main.tex:1008–1030) are **vacuous** on arlib's `Circuit`: per-node dimensions
  are allowed and `Circuit.node` already is the bilinear gate.  Smoothness,
  decomposability and structuredness of the expanded circuits (main.tex:1032)
  hold by the type.
* **Nonnegative parameters and `Z_R > 0`** (main.tex:937, 962) — replaced by the
  binders `hPnn`, `hPs`, `hQnn`, `hQs`, which say that `f_R/Z_R` is a
  distribution (`Z_R = ∑_x f_R(x)` is `wtaZP` / `wtaZQ`).  The paper's
  hypotheses **imply** them; they are slightly weaker (they also allow `f ≤ 0`
  with `Z < 0`).  The window argument uses no sign information, as recorded for
  `pc_fpras`.  `hPs` also forces every `Ω_i` nonempty, which is not a separate
  binder.
* **`I ≥ 1`** (main.tex:1034, "so assume `I ≥ 1`") — binder
  `hL : 0 < CircuitPair.steps C`.  **The single-leaf tree `I = 0` is an explicit
  non-goal**: the paper switches there to exact enumeration, a different
  deterministic algorithm.  `hL` is a visible binder on purpose: at `I = 0`,
  `perStepTol ε 0 = 0`, so `SparsifyPrior (perStepTol ε 0) _` is uninhabited
  (`hδ : 0 < 0`) and a statement without `hL` would cover that case only
  vacuously.
* **`Sparsify` / `thm:lewis_weights`** (main.tex:745–752) — binder
  `prior : SparsifyPrior (perStepTol ε I) (perStepFail η I)`, and for the uniform
  time claim `fam : SparsifyFamily` with `fam.Member prior`.  The paper **cites**
  this result; nothing in this project's libraries inhabits it at the cited size.
* **`δ ∈ (0, 1/2)`** — not a binder; `SparsifyPrior.hδ`, discharged by
  `δ = ε/(3I) ≤ 1/3`.
* **`Z_R` known to the algorithm** — not a binder; computed by the charged DP
  `Program.massDP` (main.tex:967), whose value is `circuitMass`.
* **Nondegenerate candidate matrices, positive interface dimensions** — not
  binders, deliberately.  WTA feature matrices are routinely rank-deficient, and
  `SparsifyPrior` is total on candidate sets.

## Parameters

`L = I = CircuitPair.steps C` **exactly** here: every internal node of the
paper's expanded circuit has `d² ≥ 1` product gates, so every internal node is an
active product region, and `pc_fpras`'s "Lean `L` ≥ paper `L`" caveat does not
arise.  `δ = ε/(3I)`, `η' = η/I` (main.tex:886 via 1034), so `I · η' = η` and the
union bound is tight.  `q = leafDomMax V`, `d = pairJointDim C`,
`|V| = vtreeNodes V`, `ω = prior.mmExp`. -/

/-! ## Claim (1): accuracy — can fail -/

/-- **`(1−ε) d_TV(P,Q) ≤ d̂ ≤ (1+ε) d_TV(P,Q)` with probability at least `1−η`**
(main.tex:997–998), for `P = f_P/Z_P` and `Q = f_Q/Z_Q` the distributions of the
two weighted tree automata `C`.

A measure of `Run.answerLawWTA C prior`, the law of `d̂ = DtildeWTA C R =
½ E(C_r, (Z_P^{-1}, −Z_Q^{-1}))` read off the run `Run.runLawWTA C prior`.

The mechanism (main.tex:1032, via thm:pc_fpras's proof main.tex:926–927): off the
event that some sparsification fails, `Reduction.embeds_exact` gives the root
coreset the window `(1 ± δ)^I` on every query, at `aWTA` the exact side is
`2 d_TV(P,Q)` (the `Analysis/` cross-check above), and `δ = ε/(3I)` gives
`(1 ± ε)` (`Reduction.relErr_of_calibrated`).  The union bound costs
`I · η/I = η`.  Each node's candidate matrix depends on the children's realised
coresets, so the per-step bound used is the **conditional** one:
`SparsifyPrior.bad_prob` is quantified over every candidate set and
`Run.tapeLaw` is the history-dependent sequential product, reused unchanged. -/
theorem wta_fpras_correct (hprior : Prior)
    {V : Vtree} (C : CircuitPair V 1 1)
    (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x 0 / wtaZP C)
    (hPs : ∑ x : C.Assign, C.valP x 0 / wtaZP C = 1)
    (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x 0 / wtaZQ C)
    (hQs : ∑ x : C.Assign, C.valQ x 0 / wtaZQ C = 1)
    (ε η : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < CircuitPair.steps C)
    (prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
      (perStepFail η (CircuitPair.steps C))) :
    1 - ENNReal.ofReal η
      ≤ (Run.answerLawWTA C prior).toOuterMeasure
          (Arlib.relErr ε (dTVwta C hPnn hPs hQnn hQs)) := by
    exact TvDomainReduction.Analysis.wta_fpras_correct_proof hprior (V := V) C hPnn hPs hQnn hQs ε η hε0 hε1 hη0 hη1 hL prior

/-! ## Claim (2): the arithmetic running time — cannot fail -/

/-- **The run performs
`Õ(|V| d³ (q + d + d²|V|²/ε² · log(|V|/η))² + |V| d^{2ω})` arithmetic
operations** (main.tex:998–1002, accounting main.tex:1034 via main.tex:929).

**`d³`, not the paper's `d²`, in the first term.**  This is a deliberate repair
tracking `Program.build`'s actual charge, and **the paper's `d²` bound is not what
is proved**.  The paper's expanded circuit pays `d²` per candidate row for the
product stage and applies the `d³`-wire sum layer to the `≤ M` survivors only;
`Program.build`, reused unchanged, forms the fused post-gate features (`≤ d³`
wires) on **every** candidate row — the same fused-node model gap as point 3 of
this module's first docstring.  With `polylog ≡ 1`, two leaves of dimension
`≈ d/2` and `q ≫ d²/ε² · log(3/η)`, the Lean tally is `≈ q² d³` against the
paper's `≈ |V| d² q²`, a ratio `≈ d` that no polylog absorbs.  Charging the
factored evaluation `N·d² + |C_R|·d³` in `build` would restore `d²` (and tighten
`pc_fpras_time`); that is out of scope here.

The other terms are the paper's, verbatim, and upper-bound Lean's: Lean
sparsifies `d_u ≤ d` post-gate columns rather than `O(d²)` product-stage ones, so
its `M = pairRetainedBudget C prior ≤ 9 · sizeConst · d log(2d) · I²/ε² · log(I/η)`
is dominated by the inner `d²|V|²/ε² · log(|V|/η)`, and its solver cost
`Õ(N d + d^ω)` by the bracket and `|V| d^{2ω}`.  The normalisation DP
(`O(|L| q d + I d³)`, main.tex:1034) and the dense root query are charged by
`Program.runWTA` and subsumed.

**`Õ`**: `c` is quantified after `fam` and **before every instance binder**, so it
depends only on the solver family's constants — not on the automata, `ε` or `η`.
The solver's suppressed polylogarithmic factor is left explicit as
`prior.polylog` at `d · (q + M)²`, the largest `N · d_u` any call sees; the paper
never says which logarithms its `Õ` hides.  `ω` is `prior.mmExp`.  No
normalisation binders are needed: the operation count does not depend on them.

Proof plan, recorded for the `Analysis/` pass (not a claim): a fresh per-region
recursion over the tree mirroring `Program.build` (leaf cost `(gP+gQ)·m`), since
`Analysis.build_steps_le` overcounts by a factor `q`; the side facts
`vtreeNodes V = 2 · I + 1`, `pairJointDim C ≥ 2`, `perStepFail η I ≤ 1` (for
`Analysis.retainedBudget_le_sizeBound`) and `log(2d) ≤ d`. -/
theorem wta_fpras_time (hprior : Prior) (fam : SparsifyFamily) :
    ∃ c : ℕ, ∀ {V : Vtree} (C : CircuitPair V 1 1) (ε η : ℝ),
      0 < ε → ε < 1 → 0 < η → η < 1 → 0 < CircuitPair.steps C →
      ∀ prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
          (perStepFail η (CircuitPair.steps C)),
        fam.Member prior →
        ∀ p ∈ (Run.runLawWTA C prior).support,
          (Charged.steps rate p : ℝ)
            ≤ (c : ℝ)
                * (1 + (prior.polylog
                    (pairJointDim C * (leafDomMax V + pairRetainedBudget C prior) ^ 2) : ℝ))
                * ((vtreeNodes V : ℝ) * (pairJointDim C : ℝ) ^ 3
                      * ((leafDomMax V : ℝ) + (pairJointDim C : ℝ)
                          + (pairJointDim C : ℝ) ^ 2 * (vtreeNodes V : ℝ) ^ 2 / ε ^ 2
                              * Real.log ((vtreeNodes V : ℝ) / η)) ^ 2
                    + (vtreeNodes V : ℝ) * (pairJointDim C : ℝ) ^ (2 * prior.mmExp)) := by
    exact TvDomainReduction.Analysis.wta_fpras_time_proof hprior fam

/-! ## The author's WTA result -/

/-- **Theorem 5.1 (Weighted Tree Automata)**, `thm:wta_fpras`, main.tex:996–1003.

The conjunction the paper claims, about one run of the WTA algorithm
(`Run.runLawWTA C prior`: the normalisation DP, the bottom-up coreset propagation
on the joint pair, and the root estimator at `a_TV = (Z_P^{-1}, −Z_Q^{-1})`): the
estimator `d̂` is a `(1 ± ε)` relative approximation of `d_TV(P,Q)` except on an
event of probability at most `η`; and every reachable run performs at most
`c · (1 + polylog) · (|V| d³ (q + d + d²|V|²/ε² log(|V|/η))² + |V| d^{2ω})`
arithmetic operations, with `c` fixed before the instance.

Read the section docstring above `wta_fpras_correct` first.  The departures are:
`d³` in place of the paper's `d²` in the first time term (fused node, see
`wta_fpras_time`); the single-leaf tree `I = 0` is an explicit non-goal (binder
`0 < CircuitPair.steps C`); the paper's nonnegativity and `Z_R > 0` are replaced by
the weaker distribution binders they imply; and `thm:lewis_weights` is a
hypothesis (`SparsifyPrior`, `SparsifyFamily`), not a theorem. -/
theorem wta_fpras (hprior : Prior) (fam : SparsifyFamily) :
    -- (1) accuracy, with probability at least `1 - η`
    (∀ {V : Vtree} (C : CircuitPair V 1 1)
        (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x 0 / wtaZP C)
        (hPs : ∑ x : C.Assign, C.valP x 0 / wtaZP C = 1)
        (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x 0 / wtaZQ C)
        (hQs : ∑ x : C.Assign, C.valQ x 0 / wtaZQ C = 1) (ε η : ℝ),
        0 < ε → ε < 1 → 0 < η → η < 1 → 0 < CircuitPair.steps C →
        ∀ prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
            (perStepFail η (CircuitPair.steps C)),
          1 - ENNReal.ofReal η
            ≤ (Run.answerLawWTA C prior).toOuterMeasure
                (Arlib.relErr ε (dTVwta C hPnn hPs hQnn hQs)))
    -- (2) the arithmetic running time, on every reachable outcome, with the
    --     constant fixed before the instance
    ∧ (∃ c : ℕ, ∀ {V : Vtree} (C : CircuitPair V 1 1) (ε η : ℝ),
        0 < ε → ε < 1 → 0 < η → η < 1 → 0 < CircuitPair.steps C →
        ∀ prior : SparsifyPrior (perStepTol ε (CircuitPair.steps C))
            (perStepFail η (CircuitPair.steps C)),
          fam.Member prior →
          ∀ p ∈ (Run.runLawWTA C prior).support,
            (Charged.steps rate p : ℝ)
              ≤ (c : ℝ)
                  * (1 + (prior.polylog
                      (pairJointDim C * (leafDomMax V + pairRetainedBudget C prior) ^ 2) : ℝ))
                  * ((vtreeNodes V : ℝ) * (pairJointDim C : ℝ) ^ 3
                        * ((leafDomMax V : ℝ) + (pairJointDim C : ℝ)
                            + (pairJointDim C : ℝ) ^ 2 * (vtreeNodes V : ℝ) ^ 2 / ε ^ 2
                                * Real.log ((vtreeNodes V : ℝ) / η)) ^ 2
                      + (vtreeNodes V : ℝ) * (pairJointDim C : ℝ) ^ (2 * prior.mmExp))) :=
  ⟨fun C hPnn hPs hQnn hQs ε η hε0 hε1 hη0 hη1 hL prior =>
      wta_fpras_correct hprior C hPnn hPs hQnn hQs ε η hε0 hε1 hη0 hη1 hL prior,
   wta_fpras_time hprior fam⟩

#modelClosureOfType pc_fpras
#print axioms pc_fpras

#modelClosureOfType mixture_fpras
#print axioms mixture_fpras

#modelClosureOfType wta_fpras
#print axioms wta_fpras

end TvDomainReduction

#surplusIn TvDomainReduction.Model from TvDomainReduction.pc_fpras TvDomainReduction.mixture_fpras
  TvDomainReduction.wta_fpras

/-!
HANDOFF NOTES
Review observations only; these notes do not change theorem status.
Statement match: paper — Theorem covers every instance with n ≥ 1 coordinates (δ = ε/(3n), η' = η/n; Algorithm 1 runs for t = 1..n).; Lean — Both conjuncts require `2 ≤ M.n`; n = 1 is excluded. The docstring justifies this by the circuit section's L = 0 remark. For Algorithm 1, though, n = 1 is not a different algorithm; the exclusion follows from the Lean program's own choice to keep the first leaf exact. At n = 1 the Lean run returns the exact leaf coreset, so D̃ = d_TV with probability 1 and the claim would be easy to add.
Proof trust: 2 trusted-code-base item(s), starting with Elaboration-time meta commands `#programSeal`, `#executableModule`, `#surplusIn`, `#modelClosure` and `#modelClosureOfType` (Meta/CostSeal.lean, Meta/ModelClosure.lean). They contain `partial def`s at CostSeal.lean:217 and ModelClosure.lean:22 and 190. They enforce the surface and cost-seal discipline but are not kernel-checked and are not in `mixture_fpras`'s axiom closure. They guard the statement's shape, not its truth.
Assumption boundary: 2 assumption-boundary issue(s), starting with `bad_prob` together with `embeds_of_not_bad`: with probability at least 1−η′ a call is good, and on a good draw `Embeds (1-δ) (1+δ) U (out U x)`, i.e. (1−δ)E(U,y) ≤ E(C,y) ≤ (1+δ)E(U,y) for every y. This is word for word the statement of Lemma lem:one_step (main.tex:802), and the development's own ledger says `lem:one_step` *is* `SparsifyPrior.embeds_of_not_bad`. The paper proves that lemma (main.tex:802 proof). It builds A with rows μvᵀ, notes E(U,y)=‖Ay‖₁, applies the cited thm:lewis_weights to get a sampling matrix Ỹ, and reads ‖ỸAy‖₁ back as E(C_t,y). The development assumes the result of that proof instead of proving it. Most of the substance is the cited theorem. The part that belongs to this paper is the reformulation from matrix to weighted point set: weights must be ≥ 0, the new coreset weights are Ỹ_jj·μ_j, and the at-most-m nonzero rows have to be padded to `Fin (size d)`.
Audit surface (TvDomainReduction.mixture_fpras): Every claim is present and quantified correctly. However, n = 1 is excluded, and the program is the n−1-sparsification variant of Algorithm 1. The time claim is conditional on `fam.Member`, which is a reasonable reading of the cited absolute constants. The weakening is a boundary case, not substantive.. Lean claims: For any fam of solver constants, two conjuncts. (1) For every stochastic mixture instance with n ≥ 2, ε, η ∈ (0,1), and any sampler prior at (ε/(3n), η/n), Pr[D̃ ∈ relErr ε d_TV(P_mix, Q_mix)] ≥ 1−η under the run's PMF. (2) There are c, D such that, for every such instance and every prior in fam, every reachable run costs ≤ c·(n·k·q/ε·(1+log 1/η))^D arithmetic operations.. Paper: Given ε, η ∈ (0,1), Algorithm 1 outputs D̃ with (1−ε)d_TV ≤ D̃ ≤ (1+ε)d_TV with probability at least 1−η, and runs in time polynomial in n, k, 1/ε, log(1/η), max_t|Ω_t| (main.tex:788).
Audit surface (TvDomainReduction.mixture_fpras_correct): Matches the probability, window and parameter ranges, and is generalised over samplers. The n = 1 case is dropped, and the algorithm skips the t = 1 sparsification.. Lean claims: For a stochastic instance M with n ≥ 2, normalisation proofs, ε, η ∈ (0,1), and any SparsifyPrior at (ε/(3n), η/n): 1 − η ≤ the answerLawMix mass of relErr ε (dTVmix).. Paper: (1−ε)d_TV(P,Q) ≤ D̃ ≤ (1+ε)d_TV(P,Q) with probability at least 1−η (main.tex:790–792).
Audit surface (TvDomainReduction.mixture_fpras_time): The quantifier order is correct (uniform constants), and the claim is per-outcome, which is the right shape. It is limited to n ≥ 2. Cost is counted in the ArithOp model, with the solver's cost assumed through prior.callCost and made uniform by fam.Member, which the paper implicitly assumes. The explicit main.tex:851–855 figure is not claimed.. Lean claims: Given fam, there are c, D such that, for every stochastic M with n ≥ 2, ε, η ∈ (0,1), and every prior that is a member of fam, every outcome in the support of runLawMix has charged step count ≤ c·(n k q (1/ε)(1+log 1/η))^D.. Paper: The algorithm runs in time polynomial in n, k, 1/ε, log(1/η), and max_t|Ω_t| (main.tex:794).
-/
