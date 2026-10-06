import Arlib.KnowledgeCompilation.Probabilistic.CircuitPair
import Arlib.Probability.FinDistTV
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TvDomainReduction.Model.Quantity
import TvDomainReduction.Analysis.PreludeProof

/-!
# The vocabulary of Theorem 4.1, and the quantity it is about

This is the first of the files of the audit surface.  It holds every non-library
symbol the rest of the surface uses in a definition, except for the four that
`Model/Quantity.lean` holds for a module reason recorded there (`aTV`,
`rootDistP`, `rootDistQ`, `dTV`); together the two files are the vocabulary and
the single quantity the theorem is about — the total variation distance of the
two distributions the circuits compute.  It holds no proofs: the one theorem it
states is the cross-check against the ambient library's `tvDist`, and its proof
is a delegation to its owner in `Analysis/PreludeProof.lean`, which is open.

## What is reused rather than redefined

Everything structural comes from arlib and is *not* restated here:

| paper notion | arlib declaration |
| --- | --- |
| v-tree `T` | `Arlib.KnowledgeCompilation.Probabilistic.Vtree` |
| `Ω_S` | `Vtree.Assign` / `Region.Assign` |
| smooth, decomposable, structured circuit over `T` | `Circuit V g` (by the type) |
| the *pair* `C_P, C_Q` over the **same** v-tree | `CircuitPair V gP gQ` |
| `d_S` coordinates, `P`-block then `Q`-block | `Coord gP gQ = Fin gP ⊕ Fin gQ` |
| `Φ_S` | `CircuitPair.Phi`, `Region.Phi` |
| region tree, `Ω_S`, `Φ_S`, `L = ℓ(root)` | `Region`, `Region.steps` |
| the exact weighted set `{(x,1,Φ_S x)}` | `Region.exactWPS` |
| a coreset `C_S = {(z,μ,Φ_S z)}` | `WPS ι d` |
| `E(C,y) = ∑ μ_j |⟨y, v_j⟩|` (main.tex:798) | `WPS.E` |
| `U_S = C_{S_h} × C_{S_ℓ}`, `μ_ij = λ_i ρ_j` | `WPS.tensor` |
| the free same-scope linear map `L_S` | `WPS.linMap`, `Embeds.linMap` |
| `ρ`-domain reduction for `S` (main.tex:871) | `Embeds (1-ρ) (1+ρ)` |
| the bottom-up run, `C_S` at every region | `Reduction`, `Reduction.core` |
| "Sparsify succeeded at all `L` steps" | `Reduction.Sparsifies δ` |
| Lemma `lem:pc_invariant` (main.tex:915) | `Reduction.embeds_exact` |
| the `δ = ε/(3L)` calibration | `Reduction.relErr_of_calibrated` |
| `(1 ± ε)` window | `Arlib.relErr` |
| `d_TV` | `Arlib.Probability.FinDist.tvDist` |

In particular **Lemma `lem:pc_invariant` is already proved in arlib** and must
not be restated or re-proved anywhere in this development.

## Correspondence ledger for this file

| paper | Lean |
| --- | --- |
| `q := max_i |Ω_i|` (main.tex:886) | `Vtree.leafDomMax` |
| `W = max_R max_S |G_S^R|` (main.tex:871) | `CircuitPair.regionWidth` |
| `|C| = |C_P|+|C_Q|`, gates **and** wires (main.tex:906) | `CircuitPair.totalSize` |
| `L` = number of active product regions (main.tex:886) | `CircuitPair.steps` (arlib) — see the caveat below |
| `δ = ε/(3L)` (main.tex:886) | `perStepTol` |
| `η' = η/L` (main.tex:886) | `perStepFail` |
| `Sparsify(U,m,η')` (main.tex:761) + `thm:lewis_weights` (main.tex:745) | `SparsifyPrior` |
| `m_{S_g} = O(W log(2W)/δ² log(1/η'))` (main.tex:896) | `SparsifyPrior.size` + `SparsifyPrior.size_le` |
| `M` = max rows in any internal-region coreset (main.tex:905) | `retainedBudget` (the budget) and `Reduction.maxInternalCard` (the observed max) |
| `a_TV` (main.tex:881) | `aTV` (`Model/Quantity.lean`) |
| `D̃ = ½ ∑_j μ_j |⟨a_TV, Φ_root(z_j)⟩|` (main.tex:883) | `Dtilde` |
| `d_TV(P,Q) = ½ ∑_x |P x - Q x|` (main.tex:718) | `dTV` (`Model/Quantity.lean`), cross-checked against `FinDist.tvDist` |
| `ω ≤ 2.4` (main.tex:752) | `SparsifyPrior.mmExp` + `SparsifyPrior.mmExp_le` |

The paper writes `log(2W)` with no base.  Everything below uses the natural
logarithm `Real.log`; a change of base is a constant factor and is absorbed into
`SparsifyPrior.sizeConst`.  (`Mathlib.Analysis.SpecialFunctions.Logb` is not
built in this project's Mathlib cache, which is the proximate reason.)

### Deliberate departures, recorded here and repeated in `Model/Theorem.lean`

* **`L` is `Region.steps`, the number of internal v-tree nodes, not the number of
  *active* product regions.**  arlib's `Region`/`Circuit` carries a
  product-then-sum layer at every internal node, so a paper-"inactive" region
  (neither circuit has a product gate there) is still counted.  Hence the Lean
  `L` is `≥` the paper's `L`.  Correctness is unaffected — a larger `L` means a
  smaller `δ`, a stronger per-step requirement, the same `(1 ± ε)` conclusion —
  but the two resource bounds are weakened (`M` grows like `L²` and the time
  bound carries a factor `L`).  *Statement decision.*
* **`M` is split in two.**  main.tex:905 both *defines* `M` as an observed
  maximum and *asserts* a bound on it.  Lean needs one of the two to be a
  definition, so `retainedBudget` is the static per-call budget (a function of
  `prior.size` and the region widths) and `Reduction.maxInternalCard` is the
  observed maximum; claim (2) relates them and claim (3) uses the budget.
  *Statement decision.*
* **The sparsified feature stage is the *fused* node tensor.**  The paper
  sparsifies `Ψ_S` (the product-gate values) and then applies the same-scope
  linear map `L_S` to the survivors (main.tex:894/896); arlib's `Region.node`
  fuses product-then-sum into one bilinear tensor.  A `Ψ`-stage `(1 ± δ)`
  embedding implies the fused one with the same window, by `Embeds.linMap`, so
  the per-step hypothesis used here is *weaker* than the paper's and the theorem
  correspondingly stronger.  What becomes invisible is the paper's column count
  ("the product-stage feature matrix has `O(W)` columns", main.tex:929), which is
  why `SparsifyPrior.size` is a function of the feature dimension and
  `retainedBudget` feeds it `gP + gQ ≤ 2W`.  *Modelling note.*
* **`thm:lewis_weights` is a hypothesis, not a theorem.**  The paper cites it
  (main.tex:745, to Cohen–Peng with running time from Lee–Sidford and
  Jambulapati et al.) and so does this development: it enters as
  `SparsifyPrior`.  *Model gap*, recorded again in `Model/Theorem.lean`.
* **Nonnegativity of leaf tables and sum weights is not assumed.**  The paper
  states it as part of "probabilistic circuit" (main.tex:862) but the
  propagation argument never uses it, so it appears nowhere below.  Only the
  *root* normalisation is assumed, and only to call the quantity a TV distance.
  *Statement decision* (the Lean statement is slightly more general).

## Why `SparsifyPrior` is here and not in `Model/Prior.lean`

`Model/Prior.lean` is the development-wide assumption bundle; `SparsifyPrior` is
a *parameter of this theorem*, carried explicitly in its binder list, because it
carries data (a sampler) and not only promises, and because the program has to
call it.  The run's dispatch fixes this placement.  Nothing is hidden: every
promise it makes is a field a referee reads, in this file.
-/

set_option autoImplicit false

namespace TvDomainReduction

open scoped BigOperators
open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic

/-! ## Vocabulary -/

/-! ### Static read-offs from the input

`q`, `W` and `|C|` are read off the circuit pair before the algorithm runs.  They
are the only numbers the resource claims are allowed to mention besides the
parameters and the prior's own fields. -/

/-- **`q`: the maximum leaf-domain size** `max_{i ∈ [n]} |Ω_i|` (main.tex:886).

A read-off from the v-tree alone, since an arlib v-tree leaf carries its
variable's domain `Fin m`.

Declared here rather than in arlib's `Vtree` namespace on purpose: a `Model/`
definition must live under `TvDomainReduction` for the closure checks to see it,
so none of the read-offs below is written as dot notation on a library type. -/
def leafDomMax : Vtree → ℕ
  | .leaf m => m
  | .node l r => max (leafDomMax l) (leafDomMax r)

/-- The maximum number of gates at any single region of **one** circuit:
`max_S |G_S^R|` (main.tex:871).  In this encoding the gates of scope exactly `S`
are the `g` root gates of the subcircuit sitting at `S`. -/
def gateWidth : {V : Vtree} → {g : ℕ} → Circuit V g → ℕ
  | _, _, @Circuit.leaf _ g _ => g
  | _, _, @Circuit.node _ _ _ _ g l r _ => max g (max (gateWidth l) (gateWidth r))

/-- **The size of one circuit, counting its gates *and* its wires**
(main.tex:906).  A leaf region contributes its `g` gates and the `g · m` entries
of its lookup table; a product-then-sum region contributes its `g` gates and the
`g · gl · gr` entries of its coefficient tensor, which are exactly its wires. -/
def circuitSize : {V : Vtree} → {g : ℕ} → Circuit V g → ℕ
  | _, _, @Circuit.leaf m g _ => g + g * m
  | _, _, @Circuit.node _ _ gl gr g l r _ =>
      g + g * gl * gr + circuitSize l + circuitSize r

/-- **`W`: the maximum region width of the pair**, `max_{R ∈ {P,Q}} max_S |G_S^R|`
(main.tex:871).  Hence `d_S ≤ 2W` at every region. -/
def pairWidth {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) : ℕ :=
  max (gateWidth C.P) (gateWidth C.Q)

/-- **`|C| = |C_P| + |C_Q|`**, each circuit counting its gates and its wires
(main.tex:906). -/
def pairSize {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) : ℕ :=
  circuitSize C.P + circuitSize C.Q

/-! ### Derived parameters

`L` is `CircuitPair.steps` (arlib), and the two per-step parameters are the
paper's, main.tex:886. -/

/-- **`δ = ε/(3L)`**: the per-step tolerance handed to `Sparsify` (main.tex:886). -/
noncomputable def perStepTol (ε : ℝ) (L : ℕ) : ℝ := ε / (3 * L)

/-- **`η' = η/L`**: the per-step failure probability (main.tex:886).  `L · η' = η`
exactly, so the union bound over the `L` steps is tight. -/
noncomputable def perStepFail (η : ℝ) (L : ℕ) : ℝ := η / L

/-! ### `Sparsify`, as the hypothesis it is

The paper specifies `Sparsify(U, m, η')` contractually (main.tex:761) and
instantiates it by Theorem `thm:lewis_weights` (main.tex:745), which it *cites*
rather than proves.  So it enters here, as a record of data and promises.

Five things about the shape below are decisions, not accidents.

1. **`law`, `out`, `bad` are universally quantified over the candidate set.**
   `thm:lewis_weights` is stated for one fixed matrix `A`; in the tree the
   candidate matrix at a region is a random function of the children's outcomes,
   so a per-call bound about *one* matrix does not compose.  The quantifier
   `∀ {κ d} (U : WPS κ d)` is what makes the paper's one-sentence union bound
   (main.tex:926) available at all.
2. **`out` returns a set indexed by `Fin (size d)` — exactly `size d` rows, not
   "at most".**  `thm:lewis_weights` bounds the number of *nonzero* entries of
   the sampling matrix; a variable-cardinality index type would make the run's
   randomness a dependent product over random sizes.  Zero-padding the unused
   slots (weight `0`, any feature) keeps every index type static, which is what
   lets the run's probability space be an ordinary sequential product.
3. **`δ` and `η'` are explicit parameters, and `hδ` is a field.**  `δ ∈ (0,1/2)`
   is `thm:lewis_weights`' own side condition (main.tex:747).  Carrying it here
   makes its discharge at the call site — `δ = ε/(3L) ≤ 1/3` for `ε < 1`,
   `L ≥ 1` — a visible obligation rather than a silent assumption, and keeps it
   off the headline theorem's binder list.
4. **Nondegeneracy is discharged inside the prior.**  `ℓ₁` Lewis weights need a
   nondegenerate Gram matrix (arlib's `lewis_importance_embeds` asks for
   `IsLewis`, strictly positive weights and `Nonempty ι`), and circuit feature
   matrices are routinely rank-deficient — duplicate or identically-zero gates.
   `law`/`out`/`bad` are therefore *total* on candidate sets: any instantiation
   must handle degeneracy itself (restrict to the row span, treat zero rows
   separately).  This must never migrate onto the headline theorem as a
   hypothesis about the input circuit, which the paper does not state and which
   is false for generic circuits.

   The `Nonempty ι` half of that requirement — every variable domain `Ω_i`
   nonempty, hence every candidate index type nonempty — is *not* a separate
   binder of the theorem either, and does not need to be: the paper's
   normalisation hypothesis `∑_{x ∈ Ω} P(x) = 1` (main.tex:862, carried as `hPs`
   below) is already impossible when `Ω` is empty, so it forces every leaf domain
   to be nonempty.  An instantiation may use it; the statement does not assume
   it twice.
5. **`size` is abstract.**  The paper's `m = O(W log(2W)/δ² · log(1/η'))` is
   recorded as `size_le`, so the numeric bound is visible; but every claim is
   stated against `size` itself.  The only Lewis-weight sampler proved in this
   project's libraries (arlib's `lewis_importance_embeds`) calibrates to a
   strictly larger size than the cited optimum, so the paper's `M` is *assumed
   through this field*, not proved here.

`Draw` is one fixed type rather than the call-dependent `Fin m → κ` of the
sampler: the sampler's randomness is presented in a single space, which a
concrete instantiation can always do (e.g. `Fin m → Fin K` with `K` a global
bound on candidate-set size, `out` giving weight `0` to an out-of-range row).
That is the "static sample space, history-dependent masses" shape the union
bound needs, stated uniformly. -/
structure SparsifyPrior (δ η' : ℝ) : Type 1 where
  /-- `thm:lewis_weights`' side condition on the tolerance (main.tex:747). -/
  hδ : 0 < δ ∧ δ < 1 / 2
  /-- The per-call retained-row budget, as a function of the feature dimension
  `d` only.  This is the paper's `m` (main.tex:896). -/
  size : ℕ → ℕ
  /-- The constant suppressed by the paper's `O(·)` in `m`. -/
  sizeConst : ℕ
  /-- **The paper's size bound**, `m = O(d log d / δ² · log(1/η'))`
  (main.tex:748, instantiated at main.tex:896 with `d = O(W)`). -/
  size_le : ∀ d : ℕ,
    (size d : ℝ) ≤ sizeConst * ((d : ℝ) * Real.log (2 * d) / δ ^ 2) * Real.log (1 / η')
  /-- The randomness of **one** call, in a single fixed space. -/
  Draw : Type
  /-- A placeholder draw, for the regions that consume no randomness (leaves). -/
  draw₀ : Draw
  /-- **The law of one call's draw, as a function of the candidate set.**  The
  space is static; only the masses depend on the candidate set, hence on the
  history. -/
  law : ∀ {κ d : Type} [Fintype κ] [Fintype d], WPS κ d → PMF Draw
  /-- **The surviving rows**: exactly `size d` of them, zero-padded. -/
  out : ∀ {κ d : Type} [Fintype κ] [Fintype d],
    WPS κ d → Draw → WPS (Fin (size (Fintype.card d))) d
  /-- The event on which a call fails to be an `ℓ₁` subspace embedding. -/
  bad : ∀ {κ d : Type} [Fintype κ] [Fintype d], WPS κ d → Set Draw
  /-- **The failure bound, for every candidate set** (main.tex:761, 748). -/
  bad_prob : ∀ {κ d : Type} [Fintype κ] [Fintype d] (U : WPS κ d),
    (law U).toOuterMeasure (bad U) ≤ ENNReal.ofReal η'
  /-- **The guarantee off the failure event** (main.tex:749): a `(1 ± δ)` `ℓ₁`
  subspace embedding, simultaneously for all queries. -/
  embeds_of_not_bad : ∀ {κ d : Type} [Fintype κ] [Fintype d] (U : WPS κ d) (x : Draw),
    x ∉ bad U → Embeds (1 - δ) (1 + δ) U (out U x)
  /-- The matrix-multiplication exponent `ω` (main.tex:752). -/
  mmExp : ℝ
  /-- `2 ≤ ω ≤ 2.4` (main.tex:752). -/
  mmExp_le : 2 ≤ mmExp ∧ mmExp ≤ 2.4
  /-- The constant suppressed by `Õ` in the solver's running time. -/
  costConst : ℕ
  /-- The polylogarithmic factor suppressed by `Õ` in the solver's running time.
  The paper does not say which parameters the suppressed logarithms are in; this
  field is where that silence is recorded. -/
  polylog : ℕ → ℕ
  /-- The suppressed factor does not shrink as the problem grows.  Not stated in
  the paper, and true of every polylogarithm; it is what lets the per-region
  costs be bounded by the cost at the worst-case region. -/
  polylog_mono : Monotone polylog
  /-- The arithmetic operations one call performs, as a function of the candidate
  count `N` and the feature dimension `d`. -/
  callCost : ℕ → ℕ → ℕ
  /-- **The cited solver cost** `Õ(N d + d^ω)` (main.tex:751). -/
  callCost_le : ∀ N d : ℕ,
    (callCost N d : ℝ) ≤ costConst * polylog (N * d) * ((N : ℝ) * d + (d : ℝ) ^ mmExp)

/-- **`M`: the static per-call retained-row budget, maximised over the internal
regions of the run.**

main.tex:905 both defines `M` as "the maximum number of rows retained in any
internal-region coreset" and asserts a bound on it.  This is the first half made
a definition: at an internal region with `gP + gQ` feature coordinates the
prior retains `prior.size (gP + gQ)` rows, and `M` is the largest such number
over the tree.  Claim (2) of the theorem says the *observed* maximum
(`Reduction.maxInternalCard`) never exceeds it, and claim (3) is stated with it. -/
def retainedBudget {δ η' : ℝ} (prior : SparsifyPrior δ η') :
    {V : Vtree} → {gP gQ : ℕ} → Circuit V gP → Circuit V gQ → ℕ
  | _, _, _, .leaf _, .leaf _ => 0
  | _, _, _, @Circuit.node _ _ _ _ gP lP rP _, @Circuit.node _ _ _ _ gQ lQ rQ _ =>
      max (prior.size (gP + gQ))
        (max (retainedBudget prior lP lQ) (retainedBudget prior rP rQ))

/-- `M` for a circuit pair. -/
def pairRetainedBudget {V : Vtree} {gP gQ : ℕ} {δ η' : ℝ} (C : CircuitPair V gP gQ)
    (prior : SparsifyPrior δ η') : ℕ :=
  retainedBudget prior C.P C.Q

/-- **The observed maximum**: the largest number of retained rows at any internal
(product) region of a completed run.  `0` at a leaf, since a leaf coreset is the
exact enumeration and is not an internal-region coreset. -/
def maxInternalCard : {d : Type} → {S : Region d} → Reduction S → ℕ
  | _, _, @Arlib.Approximation.Reduction.leaf _ _ _ _ _ => 0
  | _, _, @Arlib.Approximation.Reduction.node _ _ _ _ _ _ _ _ Rl Rr ι instι _ =>
      max (@Fintype.card ι instι) (max (maxInternalCard Rl) (maxInternalCard Rr))

/-! ### The root query and the estimator

`aTV` is in `Model/Quantity.lean`, below the Analysis frontier; see that file's
docstring for why. -/

/-- **The estimator `D̃`** (main.tex:883): half the evaluation functional of the
root coreset at the root query, `½ ∑_j μ_j |⟨a_TV, Φ_root(z_j)⟩|`. -/
noncomputable def Dtilde {V : Vtree} {gP gQ : ℕ} {C : CircuitPair V gP gQ}
    (R : CircuitPair.Reduction C) (jP : Fin gP) (jQ : Fin gQ) : ℝ :=
  (1 / 2) * R.core.E (aTV jP jQ)

/-! ## The quantity

The theorem is about the relative error of `D̃` as an estimator of `d_TV(P,Q)`.
`d_TV` is already in the ambient library — `Arlib.Probability.FinDist.tvDist` is
`½ ∑ x, |μ x − ν x|` — so it is *not* redefined: the two root gate values are
packaged as `FinDist`s under the paper's normalisation hypothesis
(main.tex:862), and `dTV` is the library's distance between them.

`dTV_eq_half_exactWPS_E` is the cross-check, and the one theorem this file
states: it says the exact root functional `½ · E(exactWPS_root, a_TV)` — the
quantity the propagation invariant is about — really is that TV distance, so a
referee can see the Lean statement is about a distance between distributions and
not merely about half a sum of absolute differences.

`rootDistP`, `rootDistQ` and `dTV` itself are in `Model/Quantity.lean`, below the
Analysis frontier; see that file's docstring for why. -/

/-- **The cross-check.**  The exact root functional at `a_TV` is twice the total
variation distance of the two root distributions (main.tex:927: "the exact sum in
Lemma `lem:pc_invariant` equals `2 d_TV(P,Q)`").

This is the only theorem this file states, and the only one it may: it checks
that the quantity the propagation invariant preserves is the quantity the
theorem claims to estimate.  Its content is that `⟨a_TV, Φ_root(x)⟩ = P(x) − Q(x)`
pointwise, which is where the signs of `aTV` are used. -/
theorem dTV_eq_half_exactWPS_E {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (jP : Fin gP) (jQ : Fin gQ)
    (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x jP) (hPs : ∑ x : C.Assign, C.valP x jP = 1)
    (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x jQ) (hQs : ∑ x : C.Assign, C.valQ x jQ = 1) :
    (1 / 2) * C.toRegion.exactWPS.E (aTV jP jQ) = dTV C jP jQ hPnn hPs hQnn hQs := by
    exact TvDomainReduction.Analysis.exactRoot_half_E_eq_dTV (V := V) (gP := gP) (gQ := gQ) C jP jQ hPnn hPs hQnn hQs

/-! ## The vocabulary of Theorem 1 (`thm:main_fptas`), and the quantity *it* is
about

Everything above is the vocabulary of `thm:pc_fpras` (main.tex:900), the paper's
**circuit** theorem, and **nothing above is touched**.  What follows is the
vocabulary of `thm:main_fptas` (main.tex:788–795), the paper's **mixture-of-
products** theorem, whose setting is main.tex:712–733 and whose algorithm is the
numbered Algorithm 1 at main.tex:763–784.

The engine is reused verbatim and is *not* restated: `SparsifyPrior`,
`perStepTol`, `perStepFail`, `retainedBudget`, `pairRetainedBudget`,
`maxInternalCard`, `leafDomMax`, `pairWidth`, `pairSize` from above, and from
arlib `Region`, `Region.Phi`, `Region.steps`, `Region.exactWPS`, `WPS`, `WPS.E`,
`WPS.tensor`, `diagTensor`, `Embeds`, `Reduction`, `Reduction.Sparsifies`,
`Reduction.embeds_exact` (= `lem:pc_invariant`, already proved) and
`Reduction.relErr_of_calibrated`.  `Model/Program.lean`'s `Program.build` and
`Model/Run.lean`'s `Run.tapeLaw` are reused unchanged too: both are
*query-independent*, and the extension step of Algorithm 1 (lines 5–11) is
literally the `diagTensor` instance of `WPS.tensor`, i.e. arlib's
`WPS.hadamard`, whose own docstring describes this dynamic program.

| paper | Lean |
| --- | --- |
| the input `(Ω_t)`, `α`, `β`, `P_{i,t}`, `Q_{i,t}` (main.tex:713–720) | `MixtureInstance` |
| `α, β ≥ 0` summing to `1`, every `P_{i,t}`, `Q_{i,t}` a pmf (main.tex:713–716) | `MixtureInstance.IsStochastic` |
| `k = k₁ + k₂` (main.tex:717) | `MixtureInstance.k` |
| `q = max_t |Ω_t|` (main.tex:794) | `MixtureInstance.q` |
| the v-tree the `t = 1..n` loop runs on | `mixVtree` (a left-leaning caterpillar) |
| `P`, `Q` compiled so that the loop *is* the tree recursion | `mixPair` |
| `r_t(x_t)` (main.tex:720) | the leaf tables of `mixPair`, i.e. `pTab t` / `qTab t` |
| `R_{≤t}(x_{≤t}) = R_{≤t-1} ⊙ r_t(x_t)` (main.tex:722) | `prefixFeatP`, `prefixFeatQ` |
| `R(x) = R_{≤n}(x)` | `mixFeatP`, `mixFeatQ` |
| `P(x) = ∑_i α_i ∏_t P_{i,t}(x_t)` (main.tex:714) | `mixPmfP`, and `Pmix` as a `FinDist` |
| `Q(x) = ∑_i β_i ∏_t Q_{i,t}(x_t)` (main.tex:715) | `mixPmfQ`, `Qmix` |
| `w = [α_1..α_{k₁}, −β_1..−β_{k₂}]ᵀ` (main.tex:727) | `wVec` |
| `d_TV(P,Q)` (main.tex:730–733) | `dTVmix`, the library's `FinDist.tvDist` |
| `E(C,y)` at an arbitrary query (main.tex:798) | arlib's `WPS.E` |
| `D̃ = ½ E(C_n, w)` (main.tex:782, line 13) | `DtildeMix` = `DtildeAt · (wVec ·)` |
| `δ = ε/(3n)`, `η' = η/n` (main.tex:768, line 1) | `perStepTol ε M.n`, `perStepFail η M.n` |
| `m = Θ(k log k/δ² · log(1/η'))` (main.tex:769, line 2) | `SparsifyPrior.size M.k`, bounded by `size_le` |
| `Sparsify` / `thm:lewis_weights` (main.tex:745–761) | `SparsifyPrior`, and `SparsifyFamily` in `Model/Prior.lean` |

### Six decisions recorded here and repeated in `Model/Theorem.lean`

1. **`aTV`, `Dtilde` and `dTV` are *not* reused, and must not be.**  `aTV` is
   `+1` on one designated `P` **root gate** and `−1` on one designated `Q` root
   gate; the compiled mixture pair has `k₁ + k₂` root gates, one per *component*,
   and Algorithm 1 line 13 queries them all at once with `w = (+α, −β)`.
   Reusing `aTV` here would compute the distance between two individual
   components.  So `wVec` is new, `DtildeAt` generalises `Dtilde`'s query slot
   (and `Dtilde R jP jQ = DtildeAt R (aTV jP jQ)` holds by `rfl`, which is the
   cross-check that the two agree), and the distance is `dTVmix`, not `dTV`.
   *Statement decision.*
2. **The paper's `n` Sparsify calls are `n − 1` here, and `δ` is still
   `ε/(3n)`.**  Algorithm 1 line 12 at `t = 1` sparsifies `U_1 = C_0 × Ω_1`,
   which is just the exact leaf set of `Ω_1`; §4.2's "Leaf Gates" paragraph
   (main.tex:888) keeps leaf coresets exact, and so does `Program.build` /
   `Reduction.leaf`.  The two descriptions of the same scheme therefore disagree
   on the call count (`n` versus `n − 1`), and this development follows §4.2:
   `(mixPair M).steps = M.n − 1`.  The parameters stay the paper's,
   `δ = ε/(3 M.n)` and `η' = η/M.n`, which is *more* conservative than
   `ε/(3·steps)` and leaves the union bound slack by one step.
   *Statement decision*; it is what makes the new `Reduction.Sparsifies`
   monotonicity step an `Analysis/` obligation rather than a statement change.
3. **`M.n = 1` is an explicit non-goal.**  `(mixPair M).steps = 0` there, and
   `Reduction.relErr_of_calibrated` needs `0 < steps`.  The paper's own `L = 0`
   remark (main.tex:886) says that case is computed deterministically and
   exactly — a different algorithm and a different statement.  Hence `2 ≤ M.n`.
4. **`dom`, `pTab` and `qTab` are total functions on `ℕ`.**  Only `t < n` is
   read, and `IsStochastic` only constrains `t < n`; indexing by `Fin n` would
   force `Fin`-arithmetic through the caterpillar recursion for no content.
   `mixVtree` and `mixPair` are therefore total — at `M.n = 0` they are the
   one-leaf tree over `Ω_0`, a documented junk value that no claim is about
   (every claim binds `2 ≤ M.n`).  *Lean-specific decision.*
5. **The paper's `R_{≤t}` is written out (`prefixFeatP`) rather than read off the
   compiled circuit.**  `mixPmfP` is the paper's `∑_i α_i ∏_t P_{i,t}(x_t)`,
   manifestly: the two equations of `prefixFeatP` are main.tex:722 verbatim.  The
   compiled pair `mixPair` is what the algorithm runs on, and the identity
   `(mixPair M).valP x i = mixFeatP M x i` — "the compiled circuit computes the
   paper's accumulated feature" — is a **proof obligation for `Analysis/`**, not
   a definitional coincidence; it is stated nowhere in this file because this
   file holds no proofs.  Both recursions are written over the *same* index `t`
   with the same `0`/`t+1` split, so the leaf order cannot drift between them.
   *Proof obligation, flagged.*
6. **`Pmix` and `Qmix` take their normalisation as arguments**, exactly as
   `rootDistP`/`rootDistQ` above do.  `∑_x P(x) = 1` is a *consequence* of
   `IsStochastic` — it is the product-space factorisation
   `∑_{x} ∏_t f_t(x_t) = ∏_t ∑_a f_t(a)` — but a `FinDist` field needs the proof
   term and `Model/` holds no proofs, so the consequence is carried as a binder
   and `Model/Theorem.lean` says so.  *Lean-specific decision*; deriving it is
   an `Analysis/` obligation, after which the binders become removable.

### What is *not* here, and where it went

The hybrid functional `F_t`, Lemma `lem:propagation` (main.tex:823–840) and
Lemma `lem:one_step` (main.tex:802–811) appear **nowhere** in this development.
`lem:one_step` is `SparsifyPrior.embeds_of_not_bad`; `lem:propagation` is one
node of `Reduction.embeds_exact`'s induction, which quantifies over *all* queries
at *every* region and is therefore strictly stronger than the paper's
fixed-future functional; the telescoping `(1 ± δ)^n` is that invariant's
exponent, and the calibration `δ = ε/(3n)` is `Reduction.relErr_of_calibrated`.
All of it is already proved in arlib and must not be restated.

The circuit theorem's **fused product-then-sum model gap** (point 3 of
`Model/Theorem.lean`) is **vacuous** for this theorem: every internal node of
`mixPair` carries a *diagonal* tensor, so there is no sum layer, `Ψ_S = Φ_S`, and
the paper's "apply `L_S` to the surviving rows only" step does not exist.  A
reader arriving from `pc_fpras` should not look for it. -/

/-! ### The input of Algorithm 1 -/

/-- **The input of Algorithm 1** (main.tex:713–720): `n` coordinates with domain
sizes `|Ω_t|`, `k₁` components for `P` and `k₂` for `Q`, the mixture weights `α`
and `β`, and the per-coordinate marginal tables `P_{i,t}` and `Q_{i,t}`.

Plain data: the paper's standing stochasticity hypotheses are the separate
`IsStochastic` bundle, so that the `(1 ± ε)` window claim can be read at the
generality it actually has.  `dom`, `pTab` and `qTab` are total on `ℕ` and only
`t < n` is ever read (decision 4 above). -/
structure MixtureInstance where
  /-- `n`: the number of coordinates (main.tex:713). -/
  n : ℕ
  /-- `k₁`: the number of product components of `P` (main.tex:714). -/
  k1 : ℕ
  /-- `k₂`: the number of product components of `Q` (main.tex:715). -/
  k2 : ℕ
  /-- `|Ω_t|`: the size of the `t`-th coordinate's domain, so `Ω_t = Fin (dom t)`. -/
  dom : ℕ → ℕ
  /-- `α_i`: the mixture weights of `P` (main.tex:714). -/
  alpha : Fin k1 → ℝ
  /-- `β_i`: the mixture weights of `Q` (main.tex:715). -/
  beta : Fin k2 → ℝ
  /-- `P_{i,t}`: the `i`-th `P`-component's marginal on coordinate `t`. -/
  pTab : (t : ℕ) → Fin k1 → Fin (dom t) → ℝ
  /-- `Q_{i,t}`: the `i`-th `Q`-component's marginal on coordinate `t`. -/
  qTab : (t : ℕ) → Fin k2 → Fin (dom t) → ℝ

/-- **`k = k₁ + k₂`** (main.tex:717): the total number of components, which is
also the feature dimension `d` and is *constant* along the whole run — the one
respect in which the mixture case is easier than the circuit case. -/
def MixtureInstance.k (M : MixtureInstance) : ℕ := M.k1 + M.k2

/-- **`q = max_{t ∈ [n]} |Ω_t|`** (main.tex:794), an explicit parameter of the
complexity claim. -/
def MixtureInstance.q (M : MixtureInstance) : ℕ := (Finset.range M.n).sup M.dom

/-- **The paper's standing hypotheses on the input** (main.tex:713–716): the
mixture weights are nonnegative and sum to one, and every marginal table is a
pmf on its coordinate's domain.

Kept separate from `MixtureInstance` because it is used for exactly one thing —
making the estimated quantity a total variation distance between genuine
distributions.  The `(1 ± ε)` window argument uses no sign information at all,
the same finding already recorded for the circuit case.  Only `t < n` is
constrained: the tables beyond `n` are junk the algorithm never reads. -/
structure MixtureInstance.IsStochastic (M : MixtureInstance) : Prop where
  /-- `α_i ≥ 0`. -/
  alpha_nonneg : ∀ i, 0 ≤ M.alpha i
  /-- `∑_i α_i = 1`. -/
  alpha_sum : ∑ i, M.alpha i = 1
  /-- `β_i ≥ 0`. -/
  beta_nonneg : ∀ i, 0 ≤ M.beta i
  /-- `∑_i β_i = 1`. -/
  beta_sum : ∑ i, M.beta i = 1
  /-- every `P_{i,t}` is nonnegative. -/
  pTab_nonneg : ∀ t < M.n, ∀ i a, 0 ≤ M.pTab t i a
  /-- every `P_{i,t}` is normalised on `Ω_t`. -/
  pTab_sum : ∀ t < M.n, ∀ i, ∑ a, M.pTab t i a = 1
  /-- every `Q_{i,t}` is nonnegative. -/
  qTab_nonneg : ∀ t < M.n, ∀ i a, 0 ≤ M.qTab t i a
  /-- every `Q_{i,t}` is normalised on `Ω_t`. -/
  qTab_sum : ∀ t < M.n, ∀ i, ∑ a, M.qTab t i a = 1

/-! ### The instance compiled to the v-tree the loop runs on -/

/-- **The left-leaning caterpillar v-tree over the first `t + 1` coordinates**:
`((Ω_0 × Ω_1) × Ω_2) × ⋯ × Ω_t`.

This is the v-tree Algorithm 1's `t = 1..n` loop runs on: the left child of each
internal node is the prefix region `{0,…,t−1}` and the right child is the single
coordinate `t`, so the post-order visit of the tree *is* the loop. -/
def catVtree (dom : ℕ → ℕ) : ℕ → Vtree
  | 0 => Vtree.leaf (dom 0)
  | t + 1 => Vtree.node (catVtree dom t) (Vtree.leaf (dom (t + 1)))

/-- **One side of the compiled instance**: a structured circuit over
`catVtree dom t` with `k` root gates at *every* region, one per mixture
component.

A leaf at coordinate `s` carries the lookup table `(i, a) ↦ tab s i a`, which is
the paper's local feature `r_s(a)` (main.tex:720).  An internal node carries
`diagTensor (Fin k)`, so it computes `v ↦ v ⊙ r_t` coordinatewise and there is
**no sum layer** anywhere in the circuit — which is why the extension step of
Algorithm 1 (lines 5–11) is exactly arlib's `WPS.hadamard`. -/
def catCircuit (k : ℕ) (dom : ℕ → ℕ) (tab : (t : ℕ) → Fin k → Fin (dom t) → ℝ) :
    (t : ℕ) → Circuit (catVtree dom t) k
  | 0 => Circuit.leaf (tab 0)
  | t + 1 =>
      Circuit.node (catCircuit k dom tab t) (Circuit.leaf (tab (t + 1))) (diagTensor (Fin k))

/-- The two sides paired over the one shared caterpillar, with `gP = k₁` and
`gQ = k₂` at every region.  `Coord k₁ k₂ = Fin k₁ ⊕ Fin k₂` is the paper's `ℝ^k`
with the `P`-block first (main.tex:719). -/
def catPair (M : MixtureInstance) (t : ℕ) : CircuitPair (catVtree M.dom t) M.k1 M.k2 :=
  ⟨catCircuit M.k1 M.dom M.pTab t, catCircuit M.k2 M.dom M.qTab t⟩

/-- **The v-tree of the whole instance**: the caterpillar over all `n`
coordinates, hence `n − 1` internal nodes. -/
def mixVtree (M : MixtureInstance) : Vtree := catVtree M.dom (M.n - 1)

/-- **The instance compiled to a circuit pair**, the object `Program.build` and
`Run.tapeLaw` are run on.  `(mixPair M).steps = M.n − 1`: the Lean run performs
one sparsification per *internal* region, and leaves are kept exact (decision 2
above). -/
def mixPair (M : MixtureInstance) : CircuitPair (mixVtree M) M.k1 M.k2 := catPair M (M.n - 1)

/-! ### The paper's accumulated feature, and the two mixtures -/

/-- **`R_{≤t}` on the `P`-block** (main.tex:722), written out: the Hadamard
accumulation `R_{≤t}(x_{≤t}) = R_{≤t-1}(x_{≤t-1}) ⊙ r_t(x_t)`, so that
`prefixFeatP M t x i = ∏_{s ≤ t} P_{i,s}(x_s)`.

Deliberately *not* read off the compiled circuit: this is the paper's formula, so
a referee can see that `mixPmfP` below is the paper's `P` and not the root value
of some circuit.  That the compiled pair computes it —
`(mixPair M).valP x i = mixFeatP M x i` — is an `Analysis/` obligation
(decision 5 above).  The recursion is written over the same index `t` and the
same `0`/`t+1` split as `catCircuit`, so the leaf order is shared by
construction. -/
def prefixFeatP (M : MixtureInstance) : (t : ℕ) → (catPair M t).Assign → Fin M.k1 → ℝ
  | 0, a, i => M.pTab 0 i a
  | t + 1, a, i => prefixFeatP M t a.1 i * M.pTab (t + 1) i a.2

/-- `R_{≤t}` on the `Q`-block (main.tex:722). -/
def prefixFeatQ (M : MixtureInstance) : (t : ℕ) → (catPair M t).Assign → Fin M.k2 → ℝ
  | 0, a, i => M.qTab 0 i a
  | t + 1, a, i => prefixFeatQ M t a.1 i * M.qTab (t + 1) i a.2

/-- **`R(x)` on the `P`-block**: `∏_{t ∈ [n]} P_{i,t}(x_t)`, the `i`-th product
component evaluated at `x`. -/
def mixFeatP (M : MixtureInstance) (x : (mixPair M).Assign) (i : Fin M.k1) : ℝ :=
  prefixFeatP M (M.n - 1) x i

/-- **`R(x)` on the `Q`-block**: `∏_{t ∈ [n]} Q_{i,t}(x_t)`. -/
def mixFeatQ (M : MixtureInstance) (x : (mixPair M).Assign) (i : Fin M.k2) : ℝ :=
  prefixFeatQ M (M.n - 1) x i

/-- **`P(x) = ∑_{i=1}^{k₁} α_i ∏_{t=1}^n P_{i,t}(x_t)`** (main.tex:714). -/
def mixPmfP (M : MixtureInstance) (x : (mixPair M).Assign) : ℝ :=
  ∑ i, M.alpha i * mixFeatP M x i

/-- **`Q(x) = ∑_{i=1}^{k₂} β_i ∏_{t=1}^n Q_{i,t}(x_t)`** (main.tex:715). -/
def mixPmfQ (M : MixtureInstance) (x : (mixPair M).Assign) : ℝ :=
  ∑ i, M.beta i * mixFeatQ M x i

/-- **`P` as a distribution.**  Nonnegativity and normalisation are arguments,
exactly as for `rootDistP`: both are consequences of `IsStochastic` (the second
by the product-space factorisation), but a `FinDist` field needs the proof term
and this file holds no proofs.  See decision 6 above. -/
def Pmix (M : MixtureInstance) (hnn : ∀ x, 0 ≤ mixPmfP M x) (hsum : ∑ x, mixPmfP M x = 1) :
    Arlib.Probability.FinDist (mixPair M).Assign where
  p := mixPmfP M
  p_nonneg := hnn
  p_sum := hsum

/-- **`Q` as a distribution.** -/
def Qmix (M : MixtureInstance) (hnn : ∀ x, 0 ≤ mixPmfQ M x) (hsum : ∑ x, mixPmfQ M x = 1) :
    Arlib.Probability.FinDist (mixPair M).Assign where
  p := mixPmfQ M
  p_nonneg := hnn
  p_sum := hsum

/-- **`d_TV(P,Q)`** for the two mixtures (main.tex:730–733), as the ambient
library's total variation distance — not a fresh sum of absolute differences.

The settled `dTV` cannot be reused: it is the distance between two designated
*root gates*' outputs, and the mixture pair's root gates are the `k₁ + k₂`
individual components, not `P` and `Q`. -/
noncomputable def dTVmix (M : MixtureInstance)
    (hPnn : ∀ x, 0 ≤ mixPmfP M x) (hPs : ∑ x, mixPmfP M x = 1)
    (hQnn : ∀ x, 0 ≤ mixPmfQ M x) (hQs : ∑ x, mixPmfQ M x = 1) : ℝ :=
  Arlib.Probability.FinDist.tvDist (Pmix M hPnn hPs) (Qmix M hQnn hQs)

/-! ### The query and the estimator -/

/-- **`w = [α_1,…,α_{k₁}, −β_1,…,−β_{k₂}]ᵀ`** (main.tex:727): `+α` on the
`P`-block, **minus** `β` on the `Q`-block, so that `⟨w, R(x)⟩ = P(x) − Q(x)`
pointwise (main.tex:730).

Written out rather than derived, for the same reason `aTV` is: a sign swap or a
block swap is invisible in the build and fatal to the claim. -/
def wVec (M : MixtureInstance) : Coord M.k1 M.k2 → ℝ :=
  Sum.elim M.alpha (fun i => -(M.beta i))

/-- **Half the evaluation functional of the root coreset at an arbitrary query**,
which is what Algorithm 1's RETURN line computes (main.tex:782).

This *generalises the query slot* of `Dtilde` rather than redefining the
estimator: `Dtilde R jP jQ = DtildeAt R (aTV jP jQ)` holds by `rfl`, which is the
cross-check that the two agree. -/
noncomputable def DtildeAt {V : Vtree} {gP gQ : ℕ} {C : CircuitPair V gP gQ}
    (R : CircuitPair.Reduction C) (y : Coord gP gQ → ℝ) : ℝ :=
  (1 / 2) * R.core.E y

/-- **The estimator `D̃ = ½ ∑_{(z,μ,v) ∈ C_n} μ |wᵀv| = ½ E(C_n, w)`**
(main.tex:782, Algorithm 1 line 13). -/
noncomputable def DtildeMix (M : MixtureInstance)
    (R : CircuitPair.Reduction (mixPair M)) : ℝ :=
  DtildeAt R (wVec M)

/-! ## The vocabulary of `thm:wta_fpras`, weighted tree automata

Everything above is untouched.  What follows is the vocabulary of
`thm:wta_fpras` (main.tex:996–1003), the paper's **weighted-tree-automaton**
theorem, whose setting is §5, main.tex:943–992.

**No new input type.**  On a fixed full binary tree a weighted tree automaton is
exactly arlib's `Circuit V g`:

| paper (§5) | Lean |
| --- | --- |
| tree `T = (V, E)`, leaf variables `X_i` with domain `Ω_i` (main.tex:943) | `V : Vtree`, `Vtree.leaf m` with `Ω_i = Fin m` |
| `Ω = ∏_i Ω_i` | `C.Assign` (nested pairs following the tree) |
| leaf table `h_ℓ^R : Ω_i → ℝ^{d_ℓ^R}` (main.tex:948) | `Circuit.leaf θ`, `θ : Fin d_ℓ → Fin m → ℝ` (coordinate first) |
| `[B_u^R(p,q)]_i = ∑_j ∑_k T_{u,i,j,k} p_j q_k` (main.tex:953) | `Circuit.node l r c`; `CircuitPair.valP_node` is main.tex:953 verbatim (output, left, right) |
| `d_r^R = 1` | `CircuitPair V 1 1` |
| the two automata on the **same** tree | the shared index `V` |
| `Φ_u = [h_u^P ; h_u^Q]`, `B_u` (main.tex:971–982) | `CircuitPair.Phi`, `blockTensor cP cQ` |
| `f_R(x) = h_r^R(x)` (main.tex:960) | `C.valP x 0`, `C.valQ x 0` |
| `m_u^R`, the normalisation DP (main.tex:967) | `circuitMass` |
| `Z_R = ∑_{x∈Ω} f_R(x)` (main.tex:962) | `wtaZP`, `wtaZQ` |
| `R(x) = f_R(x)/Z_R` (main.tex:964) | `wtaDistP`, `wtaDistQ` |
| `d_TV(P,Q)` (main.tex:989–991) | `dTVwta`, the library's `FinDist.tvDist` |
| `a_TV = (Z_P^{-1}, −Z_Q^{-1})` (main.tex:984) | `aWTA` |
| `d̂ = ½ E(C_r, a_TV)` (main.tex:992, 997) | `DtildeWTA` = `DtildeAt · (aWTA C)` |
| `|V|`, the number of tree nodes | `vtreeNodes` |
| `d = max_u (d_u^P + d_u^Q)` (main.tex:1002) | `pairJointDim` |
| `q`, `I = L`, `δ = ε/(3I)`, `η' = η/I`, `M` | `leafDomMax`, `CircuitPair.steps`, `perStepTol`, `perStepFail`, `pairRetainedBudget` (reused) |

The paper's proof pads every message to the global dimension `d` and expands each
bilinear gate into a layer of scalar product gates and a layer of scalar sum
gates (main.tex:1006–1030) so that the WTA fits §4's gate-level model.  On
arlib's `Circuit` neither step is needed: per-node dimensions are already
allowed, and the fused `Circuit.node` *is* the bilinear gate (`valP_node` is the
identity the expansion establishes).  Smoothness, decomposability and
structuredness hold by the type.  Neither device is formalised.

### Two decisions recorded here and repeated in `Model/Theorem.lean`

1. **`aTV`, `dTV`, `rootDistP` do not extend, and are not reused.**  They are
   built for a *self-normalised* root (`∑_x C.valP x jP = 1`); a WTA's root value
   `f_R` is unnormalised, so `pc_fpras_correct`'s hypothesis is false for a
   generic WTA and its `±1` query would estimate `½ ∑ |f_P − f_Q|`.
2. **The normaliser is computed twice, on purpose.**  The query `aWTA` uses the
   DP value `circuitMass` — what the algorithm actually computes (main.tex:967) —
   while the distributions use `Z_R := ∑_x f_R(x)`, the paper's definition.  That
   the two agree (`circuitMass C.P 0 = wtaZP C`, by bilinearity, no sign
   hypothesis) is an `Analysis/` obligation, and so is the cross-check
   `½ · C.toRegion.exactWPS.E (aWTA C) = dTVwta C …` (eq:wta-pointwise-difference,
   main.tex:986–991), which is the WTA analogue of `dTV_eq_half_exactWPS_E`.
   Neither is stated in this file, for the module reason recorded in
   `Model/Quantity.lean` and following the mixture precedent. -/

/-- **The normalisation DP `m_u^R`** (main.tex:967): at a leaf
`m_ℓ = ∑_{a ∈ Ω_i} h_ℓ(a)`, at an internal node `m_u = B_u(m_{u_L}, m_{u_R})`.

This is the value the algorithm computes for `Z_R` (as `circuitMass C.P 0`); that
it equals `∑_x f_R(x)` is an `Analysis/` obligation. -/
def circuitMass : {V : Vtree} → {g : ℕ} → Circuit V g → Fin g → ℝ
  | _, _, @Circuit.leaf _ _ θ => fun j => ∑ a, θ j a
  | _, _, @Circuit.node _ _ _ _ _ l r c =>
      fun j => ∑ p, ∑ q, c j p q * circuitMass l p * circuitMass r q

/-- **`Z_P = ∑_{x ∈ Ω} f_P(x)`** (main.tex:962), written as the paper defines it. -/
def wtaZP {V : Vtree} (C : CircuitPair V 1 1) : ℝ := ∑ x : C.Assign, C.valP x 0

/-- **`Z_Q = ∑_{x ∈ Ω} f_Q(x)`** (main.tex:962). -/
def wtaZQ {V : Vtree} (C : CircuitPair V 1 1) : ℝ := ∑ x : C.Assign, C.valQ x 0

/-- **`P(x) = f_P(x)/Z_P` as a distribution** (main.tex:964).  Nonnegativity and
normalisation are arguments, as for `rootDistP` and `Pmix`, because this file
holds no proofs.  The paper's hypotheses — nonnegative parameters and `Z_P > 0`
(main.tex:937, 962) — imply both (`div_nonneg`, `Finset.sum_div`, `div_self`);
the arguments are slightly weaker (they also allow `f ≤ 0` with `Z < 0`, which is
still a genuine distribution). -/
noncomputable def wtaDistP {V : Vtree} (C : CircuitPair V 1 1)
    (hnn : ∀ x : C.Assign, 0 ≤ C.valP x 0 / wtaZP C)
    (hsum : ∑ x : C.Assign, C.valP x 0 / wtaZP C = 1) :
    Arlib.Probability.FinDist C.Assign where
  p := fun x => C.valP x 0 / wtaZP C
  p_nonneg := hnn
  p_sum := hsum

/-- **`Q(x) = f_Q(x)/Z_Q` as a distribution** (main.tex:964). -/
noncomputable def wtaDistQ {V : Vtree} (C : CircuitPair V 1 1)
    (hnn : ∀ x : C.Assign, 0 ≤ C.valQ x 0 / wtaZQ C)
    (hsum : ∑ x : C.Assign, C.valQ x 0 / wtaZQ C = 1) :
    Arlib.Probability.FinDist C.Assign where
  p := fun x => C.valQ x 0 / wtaZQ C
  p_nonneg := hnn
  p_sum := hsum

/-- **`d_TV(P,Q)`** for the two normalised automata (main.tex:989–991), as the
ambient library's total variation distance.  Not the settled `dTV`, which is the
distance between two raw root gate outputs. -/
noncomputable def dTVwta {V : Vtree} (C : CircuitPair V 1 1)
    (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x 0 / wtaZP C)
    (hPs : ∑ x : C.Assign, C.valP x 0 / wtaZP C = 1)
    (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x 0 / wtaZQ C)
    (hQs : ∑ x : C.Assign, C.valQ x 0 / wtaZQ C = 1) : ℝ :=
  Arlib.Probability.FinDist.tvDist (wtaDistP C hPnn hPs) (wtaDistQ C hQnn hQs)

/-- **`a_TV = (Z_P^{-1}, −Z_Q^{-1})`** (main.tex:984): `+1/Z_P` on the single `P`
root coordinate, **minus** `1/Z_Q` on the single `Q` root coordinate, with `Z`
the DP value `circuitMass`.  So `⟨a_TV, Φ_r(x)⟩ = P(x) − Q(x)` pointwise
(main.tex:986).

Not the settled `aTV`, which is `±1`.  The paper's proof instead appends a unary
root sum gate of weight `Z_R^{-1}` (main.tex:1006); that gate is a same-scope
linear map applied after the root sparsification and introduces no error, so
folding it into the query gives the same number.  The input circuit's root tensor
is *not* rescaled, which would change the matrix handed to `Sparsify`.  A sign
swap or a dropped inverse here compiles and breaks the claim. -/
noncomputable def aWTA {V : Vtree} (C : CircuitPair V 1 1) : Coord 1 1 → ℝ :=
  Sum.elim (fun _ => (circuitMass C.P 0)⁻¹) (fun _ => -(circuitMass C.Q 0)⁻¹)

/-- **The estimator `d̂ = ½ E(C_r, a_TV)`** (main.tex:992, 997).  An instance of
`DtildeAt`, not a new estimator. -/
noncomputable def DtildeWTA {V : Vtree} (C : CircuitPair V 1 1)
    (R : CircuitPair.Reduction C) : ℝ :=
  DtildeAt R (aWTA C)

/-- **`|V|`, the number of nodes of the tree**, which the time bound of
`thm:wta_fpras` is stated in.  Not to be confused with the Lean binder `V`, which
is the tree itself.  On a full binary tree it is `2 · I + 1` with `I` the number
of internal nodes (`CircuitPair.steps`); that is an `Analysis/` lemma. -/
def vtreeNodes : Vtree → ℕ
  | .leaf _ => 1
  | .node l r => vtreeNodes l + vtreeNodes r + 1

/-- The joint interface dimension `max_u (d_u^P + d_u^Q)` of two circuits over the
same tree, by simultaneous recursion as in `retainedBudget`. -/
def jointDim : {V : Vtree} → {gP gQ : ℕ} → Circuit V gP → Circuit V gQ → ℕ
  | _, _, _, @Circuit.leaf _ gP _, @Circuit.leaf _ gQ _ => gP + gQ
  | _, _, _, @Circuit.node _ _ _ _ gP lP rP _, @Circuit.node _ _ _ _ gQ lQ rQ _ =>
      max (gP + gQ) (max (jointDim lP lQ) (jointDim rP rQ))

/-- **`d := max_{u ∈ V} d_u`, `d_u = d_u^P + d_u^Q`** (main.tex:969, 1002): the
joint node-interface dimension of the pair.  Differs from the settled `pairWidth`
(`pairWidth ≤ d ≤ 2 · pairWidth`).  For `CircuitPair V 1 1`, `d ≥ 2`. -/
def pairJointDim {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) : ℕ :=
  jointDim C.P C.Q

end TvDomainReduction
