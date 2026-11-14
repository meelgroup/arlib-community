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
`cv18Program`, with no assumptions beyond the input promise:

- **accuracy:** the estimate is within `1 ± ε` of the volume with probability at
  least `1 − p`;
- **cost:** every execution makes at most `⌈queryRate q⌉` membership calls, where
  `queryRate q = queryConstant · runRate q · max(1, log(1/p))`, constant included.

The query rate keeps every logarithmic factor. Dropping them gives the paper's
`O*(roundness · n³ / ε²)`.

## Where it differs from the paper

The program differs from Figure 1 in three places, each marked **Deviation** in
`Model/Pseudocode.lean`:

1. a walk's length is counted in proper steps, with a cap on proposals;
2. walk samples are moved to the target law by a rejection step with a bounded
   number of retries;
3. a run that would exceed a global query budget is stopped.

The starting variance is `ε/(64n)` rather than `1/(4n)`, and a failed run reports
`0`.

## How to read it

- `Model/` is the audit surface, read in this order:
  - `Prelude.lean`: the parameters, the body and its unit-ball promise, the
    membership oracle, what counts as accurate, the language programs are written
    in (`MembershipOracleProgram`, with `do` notation) and its output law, the
    cooling schedule, and every numeric parameter, including `queryRate`;
  - `Pseudocode.lean`: the cost model `queryCost` (each membership call costs
    `1`) and `cv18Program`;
  - `Theorem.lean`: `cv18TheoremOneOne`.

  `#modelClosureOfType cv18TheoremOneOne` and `#modelClosure cv18Program` fail
  the build if either statement unfolds to anything outside `Model/`.
- `Analysis/` holds the proof. Its end point is `volumeTheorem_finalScheduled`
  (`VolumeProofFinalScheduledTheoremAssembly.lean`), stated for the program as
  written with constructors in `ScheduledProgram.lean`; `PseudocodeBridge.lean`
  proves that program equal to `cv18Program`. Definitions used only by the proof
  are in `ModelSupport.lean`.
