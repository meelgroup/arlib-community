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

**The sampler** (`Model/Theorem.lean`), for any convex body given by a membership oracle:
`Program.sampler` (`Model/Program.lean`) runs `m` lazy hit-and-run steps; each step draws a
direction `g/‖g‖` from a standard Gaussian vector, brackets the chord by bisection, and
picks a point of the chord by rejection, with both loops capped.

- `hitAndRun_correct`: let `K` be closed, convex and bounded, contain a unit ball and have
  diameter at most `D`, and let `n ≥ 21`.  From a start that is `M`-warm outside a set of
  mass at most `ε/4`, after `m ≥ deadline n D M (ε/2)` steps, with the caps of
  `walkParams n D M ε m`, the output law is within total variation `ε` of uniform on `K`.
- `hitAndRun_queries`: on every tape and whatever answers membership, at most
  `m · (2k + r)` membership calls, with `k = ⌈log₂(16 m M n D/ε)⌉` halvings per side and
  `r = ⌈log₂(8 m M/ε)⌉` tries per step.  The calls are counted by the program's own
  `Arlib.Computation` tally: each membership call is one charged `Op.query`; each random
  number is a tallied, uncounted `Op.draw`.

**The kernel** (`Analysis/KernelTheorem.lean`).  `hitAndRun_mixes`: after

    2^64 · n² · D² · log(8M/ε²)

steps of the exact lazy walk its law is within total variation `ε` of uniform on `K`.  No
overlap, isoperimetry or conductance bound is assumed.  `finiteFacetStep_eq_step` says
that for a polytope `{x | ⟪Aᵢ, x⟫ ≤ bᵢ}` the walk that computes each chord by scanning the
facets is exactly this kernel.

## Where it differs from the paper

The proof of Lemma 8 in [Lov99] does not support its one-step overlap constant
`1 − 1/500`: its spherical-cap and chord-length estimates are both too strong.
The formalization proves `1 − 1/8000` instead. The mixing time therefore keeps the
paper's `n² D² log(M/ε)` dependence with the explicit coefficient `2^64`. The
corrected inequalities are in `Foundations/MarkovChainTheory/HitAndRunMixing/`
(`HitAndRunOverlap.lean`, `SphereCap.lean`).

**Capped chord sampling.**  The literature implements a step with a membership oracle by
bracketing the chord by binary search and sampling the bracket by rejection [Vem05, §2;
Rud13, §3.4], with a random, unbounded number of queries.  The sampler caps both loops and
stays put when every try misses; the price is the probability that some step gives up,
which the caps make at most `ε/4` (`Analysis/Accuracy.lean`).

## How to read it

- `Model/` is the audit surface, read in this order: `Prelude.lean` (state space, deadline,
  total variation, the random numbers' laws, the caps `walkParams`), `ProblemSetting.lean`
  (the body, the warm start, the target, the membership oracle), `Operations.lean` (the
  currency `Op.query`/`Op.draw` and the sealed oracle), `Program.lean` (the sampler, with
  `#programSeal`, `#executableModule`, `#modelClosure` and `#surplusIn`), `Run.lean` (the
  tape law and the output law) and `Theorem.lean`.
- `Meta/` mirrors barbarik4's: `CostSeal.lean`, `ModelClosure.lean`, `Audit.lean`.
- `Analysis/`:
  - `Tape*.lean`: the sampler as tape-program trees, equal to `Program`'s procedures; the
    random tape gives fresh randomness (`TapeLaw.lean`); measurability of the run.
  - `WalkLaw.lean`: the output law is the iterate of the step kernel.
  - `ChordPoint.lean`, `ShortChord.lean`, `GaussianDirection.lean`, `StepLaw.lean`,
    `StepCompare.lean`: one step of the sampler is within `½(1[x ∉ K_δ] + 2^{-r})` of one
    step of the exact lazy walk.
  - `Coupling.lean`, `Accuracy.lean`: the chains stay close; assembly of
    `hitAndRun_correct`.  `QueryCount.lean`: the query bound.
  - `Kernel.lean`, `KernelTheorem.lean`, `PseudocodeProof.lean`, `TheoremProof.lean`: the
    exact kernel and its mixing theorem.
- The general theory — the hit-and-run kernel, its conductance, isoperimetry and
  conductance-to-mixing — is in `ArlibCommunity/Foundations/`, mainly
  `MarkovChainTheory/HitAndRunMixing/`.
