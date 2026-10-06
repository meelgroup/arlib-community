import Arlib.KnowledgeCompilation.Probabilistic.CircuitPair
import Arlib.Probability.FinDistTV

/-!
# The root query and the quantity the theorem estimates

This is the bottom of `Model/`: the root test vector `a_TV` and the total
variation distance `d_TV(P,Q)` the theorem is about, and nothing else.

It is split out of `Model/Prelude.lean` for one reason, which is a *module*
reason and not a mathematical one.  `Model/Prelude.lean` states the cross-check
`dTV_eq_half_exactWPS_E` and delegates it to its proof-side owner
`TvDomainReduction.Analysis.exactRoot_half_E_eq_dTV`, so `Model/Prelude` imports
`Analysis/PreludeProof`.  That owner's *statement* is written in `aTV` and `dTV`,
so it has to import them — and if they lived in `Model/Prelude` the two modules
would import each other.  The four definitions below are therefore the part of
the vocabulary that sits *below* the Analysis frontier; everything else in the
paper's vocabulary stays in `Model/Prelude.lean`, which is where the
correspondence ledger for all of it is.

Both files are under `TvDomainReduction/Model/`, so the closure checks
(`#modelClosureOfType`) see this module exactly as they saw `Model/Prelude`: the
headline statement still unfolds only into `Model/` and the admitted
`Arlib.Computation`.

## Correspondence ledger for this file

| paper | Lean |
| --- | --- |
| `a_TV` (main.tex:881) | `aTV` |
| the root output of `C_P` as a pmf (main.tex:862) | `rootDistP` |
| the root output of `C_Q` as a pmf (main.tex:862) | `rootDistQ` |
| `d_TV(P,Q) = ½ ∑_x |P x - Q x|` (main.tex:718) | `dTV`, the library's `FinDist.tvDist` |

`d_TV` is **not** redefined here: `Arlib.Probability.FinDist.tvDist` is already
`½ ∑ x, |μ x − ν x|`, so the two root gate values are packaged as `FinDist`s
under the paper's normalisation hypothesis (main.tex:862) and `dTV` is the
library's distance between them.
-/

set_option autoImplicit false

namespace TvDomainReduction

open scoped BigOperators
open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic

/-- **`a_TV`** (main.tex:881): `+1` on the designated `P` root gate, `−1` on the
designated `Q` root gate, `0` on every other root-scope coordinate.

A sign error here is invisible in the build and fatal to the claim, so it is
written out rather than derived. -/
def aTV {gP gQ : ℕ} (jP : Fin gP) (jQ : Fin gQ) : Coord gP gQ → ℝ :=
  Sum.elim (fun j => if j = jP then (1 : ℝ) else 0)
           (fun j => if j = jQ then (-1 : ℝ) else 0)

/-- The distribution the `P` root gate computes, under the paper's normalisation
hypothesis (main.tex:862) that the root output *is* the pmf `P`. -/
def rootDistP {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) (jP : Fin gP)
    (hnn : ∀ x : C.Assign, 0 ≤ C.valP x jP) (hsum : ∑ x : C.Assign, C.valP x jP = 1) :
    Arlib.Probability.FinDist C.Assign where
  p := fun x => C.valP x jP
  p_nonneg := hnn
  p_sum := hsum

/-- The distribution the `Q` root gate computes. -/
def rootDistQ {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) (jQ : Fin gQ)
    (hnn : ∀ x : C.Assign, 0 ≤ C.valQ x jQ) (hsum : ∑ x : C.Assign, C.valQ x jQ = 1) :
    Arlib.Probability.FinDist C.Assign where
  p := fun x => C.valQ x jQ
  p_nonneg := hnn
  p_sum := hsum

/-- **`d_TV(P,Q)`** (main.tex:718), as the ambient library's total variation
distance between the two root distributions. -/
noncomputable def dTV {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (jP : Fin gP) (jQ : Fin gQ)
    (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x jP) (hPs : ∑ x : C.Assign, C.valP x jP = 1)
    (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x jQ) (hQs : ∑ x : C.Assign, C.valQ x jQ = 1) : ℝ :=
  Arlib.Probability.FinDist.tvDist (rootDistP C jP hPnn hPs) (rootDistQ C jQ hQnn hQs)

end TvDomainReduction
