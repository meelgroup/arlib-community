import Mathlib.Computability.NFA
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Vocabulary of `countNFA`, and the quantity it estimates

The paper (background.tex:18, 32; algorithm.tex:92) fixes a single-initial,
single-final NFA over the binary alphabet with a total order `≺` on its states,
the unrolled automaton's layers `Q^ℓ`, and the parameter block of `countNFA`.
This file states those objects and nothing else.

Correspondence ledger (paper → Lean):

* `𝒜 = (𝒬, Δ, q_I, q_F)` with order `≺` (background.tex:18) → `PaperNFA Q`, with
  `≺` the ambient `[LinearOrder Q]`; the theorem quantifies over every order.
* runs, `ℒ(q)`, `ℒ(𝒜)` (background.tex:18) → Mathlib's `NFA.eval` / `NFA.accepts`
  applied to `PaperNFA.toNFA`.  Words are `List Bool`, read left to right, so the
  paper's extension `w·b` is `w ++ [b]` (Mathlib's `NFA.eval_append_singleton`).
* `Q^ℓ` (background.tex:32: states reachable from `q_I` by a word of length `ℓ`)
  → `PaperNFA.layer`; `|Q^u| = Σ_{ℓ ≤ n} |Q^ℓ|` → `PaperNFA.unrolledCard`.
  (background.tex:32 writes the unrolled tuple as `(Q, Δ, q_F, q_I)`; that swap is
  a typo, the initial state is `q_I` throughout.)
* the selector `σ` of Remark selector (algorithm.tex:25-31) and Definition rowlocal
  (algorithm.tex:191-199) → `Selector`, whose admissibility is a field.
* the parameter block (algorithm.tex:92) → `Params` and `params`.
* `|ℒ_n(𝒜)|` → `sliceCount`.
-/

namespace Nfa

/-! ## Vocabulary -/

/-- **The paper's NFA** (background.tex:18): a finite state type `Q`, a transition
relation `Δ ⊆ Q × {0,1} × Q` given by its indicator (`delta q' b q = true` iff
`(q', b, q) ∈ Δ`), one initial state and one final state.

The total order `≺` used for tie-breaking is the `[LinearOrder Q]` instance at the
use site.  The general multi-initial / multi-final / larger-alphabet case, which the
paper reduces to this one "without loss of generality" (introduction.tex:229-230),
is not part of the claim. -/
structure PaperNFA (Q : Type) where
  /-- `delta q' b q = true` iff `(q', b, q) ∈ Δ`. -/
  delta : Q → Bool → Q → Bool
  /-- The initial state `q_I`. -/
  qI : Q
  /-- The final state `q_F`. -/
  qF : Q

namespace PaperNFA

variable {Q : Type}

/-- The same automaton as a Mathlib `NFA` over `Bool`: start set `{q_I}`, accepting
set `{q_F}`.  The language of a state `q` (the paper's `ℒ(q)`) is
`{w | q ∈ A.toNFA.eval w}`, and `ℒ(𝒜) = A.toNFA.accepts`. -/
def toNFA (A : PaperNFA Q) : NFA Bool Q where
  step q b := {q' | A.delta q b q' = true}
  start := {A.qI}
  accept := {A.qF}

/-- `Q^ℓ` (background.tex:32): the states reachable from `q_I` by some word of length
exactly `ℓ`.  Forward reachability only, exactly as the paper's `Q^u`; states that
cannot reach `q_F` are kept, since `|Q^u|` enters the parameters. -/
def layer (A : PaperNFA Q) (ℓ : ℕ) : Set Q :=
  {q | ∃ w : List Bool, w.length = ℓ ∧ q ∈ A.toNFA.eval w}

/-- `|Q^u| = Σ_{0 ≤ ℓ ≤ n} |Q^ℓ|`, the number of states of the unrolled automaton
for length `n`.  It enters `γ` and `θ` of the parameter block. -/
noncomputable def unrolledCard [Finite Q] (A : PaperNFA Q) (n : ℕ) : ℕ :=
  ∑ ℓ ∈ Finset.range (n + 1), (A.layer ℓ).ncard

end PaperNFA

/-- **An admissible selector** (eq. union_sel, Remark selector algorithm.tex:25-31;
Definition rowlocal algorithm.tex:191-199).

For a state `q` and a sample `u = w·b`, `pick q w b` names the predecessor `q'`
whose extended sample `w·b` survives the union step.  It is a function of
`(q, w, b)` only — not of the random samples — which is what Definition rowlocal
asks of a witness routine, and here it is enforced by the type.  The layer index of
the paper's `σ(u, q^i)` is `|w| + 1`, so it is not a separate argument.

`pick_sound` and `pick_complete` say it lands in the candidate set
`W(w, q) = {q' | (q', b, q) ∈ Δ ∧ w ∈ ℒ(q')}` and answers whenever that set is
nonempty.  The paper's own algorithm (eq. union) is the selector returning the
`≺`-least candidate; the theorem holds for every admissible selector. -/
structure Selector {Q : Type} (A : PaperNFA Q) where
  /-- The predecessor chosen for the sample `w·b` at state `q`. -/
  pick : Q → List Bool → Bool → Option Q
  /-- The chosen predecessor is a candidate: a `b`-predecessor of `q` accepting `w`. -/
  pick_sound : ∀ q w b q', pick q w b = some q' →
    A.delta q' b q = true ∧ q' ∈ A.toNFA.eval w
  /-- A predecessor is chosen whenever a candidate exists. -/
  pick_complete : ∀ q w b q', A.delta q' b q = true → q' ∈ A.toNFA.eval w →
    (pick q w b).isSome

/-- **The parameter block of `countNFA`** (algorithm.tex:92), as the natural numbers
the algorithm runs with: block size `β`, number of blocks `γ`, repetitions
`α = βγ`, interrupt threshold `θ`, and number of independent core runs `μ`. -/
structure Params where
  /-- `β`: the number of repetitions averaged in one block mean. -/
  β : ℕ
  /-- `γ`: the number of block means whose median is taken. -/
  γ : ℕ
  /-- `α = βγ`: the number of independent sample sets per state. -/
  α : ℕ
  /-- `θ`: the stored-sample threshold of line:interrupt. -/
  θ : ℕ
  /-- `μ`: the number of independent runs of `countNFAcore`. -/
  μ : ℕ

/-- **The parameters exactly as algorithm.tex:92 fixes them**:
`β = ⌈64n / (ε²(1−ε))⌉`, `γ = ⌈5 ln(16|Q^u|)⌉`, `α = βγ`, `θ = ⌈16α(1+ε)|Q^u|⌉`,
`μ = ⌈8 ln(1/δ)⌉`.

The constant in `β` is `64n`, not the `16n` of an earlier version of the paper;
introduction.tex:165-171 records that correction. -/
noncomputable def params {Q : Type} [Finite Q] (A : PaperNFA Q) (n : ℕ) (ε δ : ℝ) :
    Params :=
  let Qu : ℝ := (A.unrolledCard n : ℝ)
  let β : ℕ := ⌈64 * (n : ℝ) / (ε ^ 2 * (1 - ε))⌉₊
  let γ : ℕ := ⌈5 * Real.log (16 * Qu)⌉₊
  { β := β
    γ := γ
    α := β * γ
    θ := ⌈16 * ((β * γ : ℕ) : ℝ) * (1 + ε) * Qu⌉₊
    μ := ⌈8 * Real.log (1 / δ)⌉₊ }

/-! ## The quantity -/

/-- **`|ℒ_n(𝒜)|`**: the number of binary words of length `n` accepted by the
automaton, i.e. with `q_F` reachable from `q_I` along a run reading them.

Defined from the transition relation alone, through Mathlib's `NFA.accepts`, and not
from the unrolled automaton or the algorithm.  The set is finite (it lies inside the
`2^n` words of length `n`), so `ncard` is its true cardinality. -/
noncomputable def sliceCount {Q : Type} (A : PaperNFA Q) (n : ℕ) : ℕ :=
  {w : List Bool | w.length = n ∧ w ∈ A.toNFA.accepts}.ncard

end Nfa
