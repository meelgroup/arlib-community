/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `ArlibCommunity.Algorithms.TPA` — the Tootsie Pop Algorithm

Part of the `ArlibCommunity.Algorithms` area; see `ArlibCommunity/Algorithms.lean`.

**Paper.** Mark Huber and Sarah Schott, *Using TPA for Bayesian Inference*,
Bayesian Statistics 9, OUP, 2010, pp. 257–282 (arXiv:0907.2989) — `[Hub10]`.
The two-phase run-count schedule of `ArlibCommunity.Algorithms.TPA.TwoPhase` is
also analysed in Mark Huber, *Approximation Algorithms for the Normalizing
Constant of Gibbs Distributions*, Ann. Appl. Probab. **25**(2):974–985, 2015
(arXiv:1206.2689) — `[Hub15]`; the "Theorem 5" that file refers to is numbered
as in [Hub15].  Every statement below is proved from scratch.

The Tootsie Pop Algorithm (Huber) estimates a ratio of measures
`μ(B)/μ(B')` for a *centre* `B'` inside a *shell* `B`, given a family of nested
sets interpolating between them whose measure varies continuously.  It replaces
the classical self-reducibility product estimator, whose output is a product of
scaled binomials, by a single Poisson random variable — which is why its analysis
is sharp and why it is worth having as reusable infrastructure.

This sub-area holds the algorithm-independent part: the law of TPA's counter.  The
work of exhibiting a nested family for a particular counting problem, and of
showing that one contraction really does multiply the measure by a uniform
factor, belongs to the project that uses TPA.

## Modules

* `ArlibCommunity.Algorithms.TPA.Count` — the closed form `tpaTail` for `P(U₁ ⋯ U_m > c)`, its
  one-dimensional integral recursion, the resulting Poisson law for the number of
  contractions, and almost-sure termination.
* `ArlibCommunity.Algorithms.TPA.UniformProduct` — the identification of `tpaTail` with the
  probability it is named for: on the product of `m` copies of `Uniform(0,1)` the
  event `{U₁ ⋯ U_m > c}` really does have measure `tpaTail m c` (for `0 < c < 1`),
  and consecutive differences are the Poisson masses `poissonPMF (ln(1/c))`.
* `ArlibCommunity.Algorithms.TPA.TwoPhase` — the arithmetic of the two-phase run-count schedule: the
  exact phase-one threshold, the phase-two budget inequalities (which force
  `1 ≤ A`), and the passage from additive log accuracy to relative accuracy.
-/
import ArlibCommunity.Algorithms.TPA.Count
import ArlibCommunity.Algorithms.TPA.UniformProduct
import ArlibCommunity.Algorithms.TPA.TwoPhase
