import Formalization3sum.Model.Prelude
import Formalization3sum.Model.Operations
import Formalization3sum.Meta.CostSeal
import Formalization3sum.Meta.ModelClosure
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-!
# Direct fallback; the sparse construction is not represented

Correspondence ledger for `algorithmTranscript` (04-general.tex:263–335,
342–397; 02-matrix.tex:101–125,132–158,198–260,304–327,360–364):
* 04-general.tex:69,361, direct treatment of `D = 1` and bounded exceptional
  dimensions -> `directEntry` and `directRun`. This code takes that direct path
  for every `D`; no small-dimension cutoff or sparse-path branch is implemented.
  `directEntry` folds over the
  `D` finite inner coordinates and accumulates their products; `directRun` iterates
  over the sorted wanted positions and appends each result. Both loops stop
  at the end of their finite ranges. There are no randomized draws in the
  paper algorithm. This fallback has `D` and `W.card` iterations.
* Paper `N,D,X,Y,W` -> `Model.Input N D`; the requested value is the integer
  returned by `directEntry` and paired with its position by `directRun`.
  Paper `B`, `ε`, `κ`, and `γ` constrain callers in `Model.Theorem`, not this
  direct computation.
* Paper `m = ⌈log₄ D⌉`, `L = 21m`, `t = ⌈m/9⌉`, `N₀`, `K`, and `K₀` ->
  `Model.paddedExponent`, `fixedDepth`, `fixedThreshold`, `blockRows`,
  `innerSets`, and `bandBlocks`. None controls this direct branch. The general
  construction's `c > 10`, `0 < θ < 0.9`, `L = ⌈cm⌉`, `t = ⌈θm⌉`, and
  `q = κ/2` have no executable selection here. The technical tile-fit test
  and the small-`m` cutoff likewise have no executable selection.
* Transcript steps 0–8, apart from the direct exception, are absent: no zero
  padding, outer tiling, deterministic distinct-`Q` assignment, shared
  Schönhage encodings, box initialization or recurrence, trie fill, query
  location, or low-order/box partition is computed here. In the paper, encoding
  loops visit each row or column band and each of the `10^L` term strings;
  the tile loop visits every band pair, initializes star-free boxes, then
  fills boxes by increasing star count and stops after the final eligible
  box; the query loop visits each member of `W`, enumerates all low-order
  leaves (`d < t`) and all selected high-order boxes, then stops after its
  last requested position. None of those loops occurs in this Lean term.
  Consequently this file does **not** implement the paper's sparse algorithm.
  `Operations.Op` and `Operations.Cell` name RAM instructions and storage,
  but `Operations.lean` exposes no `Charged` wrappers for input reads, signed
  arithmetic, answer writes, or indexed storage. `#programSeal` forbids
  calling `Charged.op` directly from this namespace, so the missing charged
  steps cannot be supplied honestly in this file alone. In particular, merely
  selecting the `.load`, `.mul`, or `.store` constructors of `Op` would not
  execute those instructions: a wrapper must define their result and charge
  in `Operations.lean`. The direct branch also needs such wrappers; its test
  `k < D` and matrix reads currently inspect transparent values for free.
  The two definitions below preserve the fallback's returned value but use
  `pure` for scalar arithmetic, input reads, enumeration, sorting, and answer construction.
  Their zero tally is **not** an operation count for the paper. The seal does
  not detect work on these transparent `Matrix`, `Finset`, and `Int` values.
  This is an
  explicit model gap, not a claim that these operations take zero time. In
  particular the loop combinators charge only their bodies, and both bodies
  presently use `pure` for their work. Thus `directRun` cannot justify either
  subquadratic headline bound, even though it returns the requested entries.
  `Model.Theorem` currently applies its time operators to this same
  `directRun`, so a proof of those inequalities would measure this incomplete
  tally rather than the paper's computation. This requires a change to the
  operation interface and then to the theorem's program reference in a later
  pass; adding analysis lemmas alone cannot repair the measured object.
  The RAM word-width and reached-word invariant are not represented here.
  The paper has no randomized draws: none are per-call, per-state, per-layer,
  or per-run. The absent sparse branch is a model gap and proof obligation;
  using the direct exception is a statement decision only for bounded `D`.
-/

set_option autoImplicit false

namespace Formalization3sum.Program

open Formalization3sum.Model
open Formalization3sum.Model.Operations
open Arlib.Computation

/-- The direct inner product, used by the paper only for small dimensions. -/
def directEntry {N D : ℕ} (a : Input N D) (p : Fin N × Fin N) :
    Charged Operations.Op Operations.Cell ℤ :=
  Charged.foldl (fun acc k =>
    pure (acc + a.X p.1 k * a.Y k p.2)) (List.finRange D) 0

/-- Value-producing direct fallback. Its uncharged operations are the model gap
described above; this is not a costed implementation of the paper. -/
def directRun {N D : ℕ} (a : Input N D) :
    Charged Operations.Op Operations.Cell (List ((Fin N × Fin N) × ℤ)) :=
  Charged.foldl (fun answers position => do
    let v ← directEntry a position
    pure ((position, v) :: answers))
    (a.W.sort (Prod.Lex (· < ·) (· ≤ ·))) []

end Formalization3sum.Program

#programSeal Formalization3sum.Program
#executableModule Formalization3sum.Model.Program
#surplusIn Formalization3sum.Model.Program from Formalization3sum.Program.directRun
