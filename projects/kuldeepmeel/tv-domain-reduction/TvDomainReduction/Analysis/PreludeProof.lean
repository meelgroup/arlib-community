import Arlib.KnowledgeCompilation.Probabilistic.CircuitPair
import Arlib.Probability.FinDistTV
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TvDomainReduction.Model.Quantity

/-!
Proof-side owner for the cross-check `TvDomainReduction.dTV_eq_half_exactWPS_E`.

This module sits *below* `Model/Prelude.lean`, which delegates to it, so it may
import only the part of the vocabulary its statement is written in —
`Model/Quantity.lean`.  Importing `Model/Prelude` or anything above it (the
`Interface/` bridges, `Model/Run`) would close an import cycle, since
`Model/Prelude` imports this file.
-/

set_option autoImplicit false

namespace TvDomainReduction.Analysis

open Arlib.Approximation
open Arlib.KnowledgeCompilation.Probabilistic

/-- Proof-side owner for `TvDomainReduction.dTV_eq_half_exactWPS_E`; its statement is fixed by the proof charter.

PAPER: main.tex:877-880 — `d_TV(P,Q) = ½ ∑ₓ |⟨a_TV, Φ_root(x)⟩|`. -/
theorem exactRoot_half_E_eq_dTV {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ)
    (jP : Fin gP) (jQ : Fin gQ)
    (hPnn : ∀ x : C.Assign, 0 ≤ C.valP x jP) (hPs : ∑ x : C.Assign, C.valP x jP = 1)
    (hQnn : ∀ x : C.Assign, 0 ≤ C.valQ x jQ) (hQs : ∑ x : C.Assign, C.valQ x jQ = 1) :
    (1 / 2) * C.toRegion.exactWPS.E (aTV jP jQ) = dTV C jP jQ hPnn hPs hQnn hQs := by
  -- `E` of the exact set is `∑ₓ |⟨a_TV, Φ(x)⟩|`, and `⟨a_TV, Φ(x)⟩ = P(x) − Q(x)`.
  rw [dTV, Arlib.Probability.FinDist.tvDist_apply, Region.exactWPS, WPS.E_exact]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [dot, Fintype.sum_sum_type, aTV, Sum.elim_inl, Sum.elim_inr, ite_mul, one_mul,
    neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [rootDistP, rootDistQ, CircuitPair.valP, CircuitPair.valQ, sub_eq_add_neg]

end TvDomainReduction.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `exactRoot_half_E_eq_dTV` via `WPS.E_exact` and `FinDist.tvDist_apply`
-/
