# Hit-and-run analysis

`Model/` is the compact audit surface.  This directory contains the arguments
behind it:

- `PseudocodeProof.lean` proves the direction/chord semantics, Markov property,
  stationary uniform law, and equality of the finite-facet implementation with
  the denotational kernel.
- `TheoremProof.lean` assembles the unconditional total-variation theorem.
- `AuditCheck.lean` checks the model closure and prints the axioms of every
  public capstone.
- The general theory it rests on — the hit-and-run kernel, its conductance and mixing,
  localization, isoperimetry, and conductance-to-mixing — lives in
  `ArlibCommunity/Foundations/` (see `Foundations/MarkovChainTheory/HitAndRunMixing/`).

## The paper's printed constant

The proof in [Lov99] does not justify the printed `1 - 1/500` local-overlap
constant: its cap-probability and chord-length estimates are both too strong.
The formal chain proves a corrected `1 - 1/8000` local bound and consequently
uses the conservative deadline

`2^64 * n^2 * D^2 * log (8*M/eps^2)`.

This preserves the claimed asymptotic dependence while avoiding a false or
unsupported literal transcription.  The discrepancy and its corrected
inequalities are documented in `HitAndRunOverlap.lean` and `SphereCap.lean`.
