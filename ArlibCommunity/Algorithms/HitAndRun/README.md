# Hit-and-run

**Paper.** László Lovász. *Hit-and-run mixes fast.* Mathematical Programming
86 (1999), 443–461. Key `[Lov99]` in `REFERENCES.md`.

## The problem

Sample a nearly uniform point of a convex body `K ⊆ ℝⁿ`. Hit-and-run is a Markov
chain on `K`: from the current point `x`, pick a direction uniformly at random on
the unit sphere, and move to a uniformly random point of the chord of `K` through
`x` in that direction. The question is how many steps it takes, from a warm
start, to get within total variation `ε` of the uniform distribution on `K`.

## What is proved

`hitAndRun_mixes` (`Model/Theorem.lean`). Let `K` be closed, convex and bounded,
contain a unit ball, and have diameter at most `D`, and let `n ≥ 21`. Start the
lazy walk from a law that is at most `M` times uniform outside a set of mass at
most `ε/2`. After

    2^64 · n² · D² · log(8M/ε²)

steps its law is within total variation `ε` of uniform on `K`. No overlap,
isoperimetry or conductance bound is assumed.

`finiteFacetStep_eq_step` says that for a polytope `{x | ⟪Aᵢ, x⟫ ≤ bᵢ}` the walk
that computes each chord by scanning the facets is exactly this kernel.

## Where it differs from the paper

The proof of Lemma 8 in [Lov99] does not support its one-step overlap constant
`1 − 1/500`: its spherical-cap and chord-length estimates are both too strong.
The formalization proves `1 − 1/8000` instead. The mixing time therefore keeps the
paper's `n² D² log(M/ε)` dependence with the explicit coefficient `2^64`. The
corrected inequalities are in `Foundations/MarkovChainTheory/HitAndRunMixing/`
(`HitAndRunOverlap.lean`, `SphereCap.lean`).

## How to read it

- `Model/` is the audit surface: `ProblemSetting.lean` (the input), `Pseudocode.lean`
  (the walk) and `Theorem.lean` (the results above).
- `Analysis/PseudocodeProof.lean` proves the direction/chord formula, that the
  kernel is Markov with the uniform law stationary, and `finiteFacetStep_eq_step`.
- `Analysis/TheoremProof.lean` assembles `hitAndRun_mixes`.
- `Analysis/AuditCheck.lean` checks the model closure and prints the axioms.
- The general theory — the hit-and-run kernel, its conductance, isoperimetry and
  conductance-to-mixing — is in `ArlibCommunity/Foundations/`, mainly
  `MarkovChainTheory/HitAndRunMixing/`.
