# Hit-and-run analysis

`Model/` is the compact audit surface.  This directory contains the arguments
behind it:

- `PseudocodeProof.lean` proves the direction/chord semantics, Markov property,
  stationary uniform law, and equality of the finite-facet implementation with
  the denotational kernel.
- `TheoremProof.lean` assembles the unconditional total-variation theorem.
- `AuditCheck.lean` checks the model closure and prints the axioms of every
  public capstone.
- `Background/` is the transitive proof background needed because these
  continuous-MCMC modules are not yet present on MEELGroup Arlib `main`.

## Scope of the background

The 81 Lean modules under `Background/Arlib/` are the exact transitive source
closure of the unconditional mixing capstone and finite-facet execution
capstone, ported from commit
`d34b0f452e04d91a74212dd9852e58550cef29c0`.  Imports were mechanically moved
under the `ArlibCommunity.Algorithms.HitAndRun.Analysis.Background` module
prefix so they can coexist with the current Arlib dependency.  No unrelated
arlib-community theories are retained.

The chain covers the measurable kernel, reversibility and invariance, warm
starts, total variation, local overlap, localization, one-dimensional and
convex-body isoperimetry, conductance, lazy-chain mixing, and the final
unconditional theorem.

## The paper's printed constant

The proof in [Lov99] does not justify the printed `1 - 1/500` local-overlap
constant: its cap-probability and chord-length estimates are both too strong.
The formal chain proves a corrected `1 - 1/8000` local bound and consequently
uses the conservative deadline

`2^64 * n^2 * D^2 * log (8*M/eps^2)`.

This preserves the claimed asymptotic dependence while avoiding a false or
unsupported literal transcription.  The discrepancy and its corrected
inequalities are documented in `HitAndRunOverlap.lean` and `SphereCap.lean`.
