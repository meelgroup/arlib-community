# Cousins–Vempala Gaussian cooling

**Paper.** Ben Cousins, Santosh Vempala. *Gaussian Cooling and `O*(n³)`
Algorithms for Volume and Gaussian Volume.* SIAM Journal on Computing
47(4):1454–1484, 2018. Key `[CV18]` in `REFERENCES.md`.

## The problem

Estimate the volume of a convex body `K ⊆ ℝⁿ` to within a factor `1 ± ε`, with
probability at least `1 − p`, using only a membership oracle for `K`. `K` is
assumed to contain the unit ball and to be well rounded: the second moment of the
uniform distribution on `K` is at most `roundness · n`.

The algorithm (Figure 1 of [CV18]) starts from a narrow Gaussian restricted to
`K` and widens it in phases until it is close to uniform on `K`. In each phase it
draws samples with a random walk, estimates the ratio between consecutive
Gaussian integrals, and multiplies the ratios. Theorem 1.1 takes the median of
`⌈8 log(1/p)⌉` independent runs.

## What is proved

`cv18TheoremOneOne` (`Model/Theorem.lean`), Theorem 1.1 of [CV18] for the program
`Program.estimator`, run on a random tape, with no assumptions beyond the input
promise:

- **accuracy** (`cv18_correct`): the estimate is within `1 ± ε` of the volume with
  probability at least `1 − p` over the tape;
- **cost** (`cv18_queries`): every execution, on every tape, makes at most
  `⌈queryRate q⌉` membership calls, where
  `queryRate q = queryConstant · runRate q · max(1, log(1/p))`, constant included.
  The calls are counted by the program's own `Arlib.Computation` tally: each
  membership call is one charged `Op.query`.

The query rate keeps every logarithmic factor. Dropping them gives the paper's
`O*(roundness · n³ / ε²)`.

## Where it differs from the paper

The program differs from Figure 1 in three places, each marked **Deviation** in
`Model/Program.lean`:

1. a walk's length is counted in proper steps, with a cap on proposals;
2. walk samples are moved to the target law by a rejection step with a bounded
   number of retries;
3. a run that would exceed a global query budget is stopped.

The starting variance is `ε/(64n)` rather than `1/(4n)`, and a failed run reports
`0`.

## How to read it

- `Model/` is the audit surface, read in this order:
  - `Prelude.lean`: the parameters, the body and its unit-ball promise, the
    membership oracle, what counts as accurate, the cooling schedule, the sampling
    laws, and every numeric parameter, including `queryRate`;
  - `Operations.lean`: the currency, `Op.query` (one membership call) and
    `Op.draw` (one random number, tallied but not counted), and the sealed oracle:
    the body's membership answers and a random tape, readable only through the
    charged operations `ask`, `drawBall`, `drawGaussian`, `drawUnit`;
  - `Program.lean`: the algorithm `Program.estimator`, a charged
    `Arlib.Computation` computation of the oracle.  `#programSeal` (`Meta/CostSeal.lean`) fails the build
    if any declaration of the program reaches the oracle's private fields, a
    computation's value or tally, or a hand-charged operation;
  - `Run.lean`: the tape law (independent rounds of a unit-ball point, a standard
    Gaussian vector and a uniform number), one execution `execution q member t`, and
    the output law `estimate q I oracle`;
  - `Theorem.lean`: `cv18_correct`, `cv18_queries` and `cv18TheoremOneOne`.

  `#modelClosureOfType cv18TheoremOneOne` fails the build if the statement unfolds
  to anything outside `Model/`.
- `Analysis/` holds the proof.
  - The accuracy proof's end point is `volumeTheorem_finalScheduled`
    (`VolumeProofFinalScheduledTheoremAssembly.lean`), stated for the program tree
    written with constructors in `ScheduledProgram.lean`; `PseudocodeBridge.lean`
    proves it equal to the program tree `cv18Program` (`OracleProgram.lean`), and
    `OracleProgramTheorem.lean` states Theorem 1.1 for that tree.
  - The `Tape*.lean` files connect it to the program of `Model/`:
    `TapeAlgorithm.lean` writes the algorithm as tape-program trees and proves that
    they are `Program`'s procedures; `TapeInterp.lean` runs them on the oracle and
    counts their calls; `TapeLaw.lean` proves that a run on the random tape has the
    law of drawing each random number fresh; `TapeDrawLaws.lean` and
    `TapeRefines.lean` turn the tape's random numbers into the tree's point draws;
    `TapeMeasurability.lean` and `TapeAlgorithmMeasurable.lean` show the run is
    measurable in the tape; `TapeBridge.lean` assembles the output law and the query
    bound.
  - Definitions used only by the proof are in `ModelSupport.lean`.
