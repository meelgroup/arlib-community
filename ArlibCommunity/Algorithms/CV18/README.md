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
- **cost:** every execution makes at most `⌈queryConstant · queryRate q⌉` membership
  calls.

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

- `Model/README.md` is the guide to the audit surface (`Prelude.lean`,
  `Pseudocode.lean`, `Theorem.lean`).
- `Analysis/README.md` is the guide to the proof and records its dependency audit.
