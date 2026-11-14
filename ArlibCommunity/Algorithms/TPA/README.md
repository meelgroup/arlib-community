# The Tootsie Pop Algorithm (TPA)

**Paper.** Mark Huber, Sarah Schott. *Using TPA for Bayesian Inference.*
Bayesian Statistics 9, OUP, 2010, pp. 257–282. arXiv:0907.2989. Key `[Hub10]` in
`REFERENCES.md`.

The two-phase run-count schedule in `TwoPhase.lean` is also analysed in Mark
Huber, *Approximation Algorithms for the Normalizing Constant of Gibbs
Distributions*, Annals of Applied Probability 25(2):974–985, 2015,
arXiv:1206.2689, key `[Hub15]`; the "Theorem 5" that file refers to is
[Hub15]'s.

## The problem

Estimate the ratio `μ(B)/μ(B')` of the measures of a *shell* `B` and a *centre*
`B' ⊆ B`, given a nested family of sets between them whose measure varies
continuously. One run of TPA starts from a random point of the shell and
repeatedly shrinks to the smallest set of the family that still contains a fresh
random point, until it reaches the centre. The number of shrinking steps is
Poisson with mean `A = ln(μ(B)/μ(B'))`, so averaging runs estimates `A`.

## What is proved

This area holds the part that does not depend on the counting problem. The work
of exhibiting the nested family, and of showing that one step multiplies the
measure by a uniform factor, belongs to the project that uses TPA.

- `Count.lean`: the closed form `tpaTail m c` of `P(U₁ ⋯ U_m > c)` for independent
  `Uniform(0,1)` variables, its integral recursion, and almost-sure termination.
- `UniformProduct.lean`: `tpaTail m c` really is that probability, and the number
  of steps is Poisson (`prob_exactly_eq_poissonPMF`).
- `TwoPhase.lean`: the arithmetic of the two-phase run-count schedule, and the
  passage from additive error in `A` to relative error in `e^A`.

## Layout

TPA predates the `Model/` + `Analysis/` layout of the other algorithms and has no
audit surface: its results are lemmas for other analyses, not a theorem about a
program.
