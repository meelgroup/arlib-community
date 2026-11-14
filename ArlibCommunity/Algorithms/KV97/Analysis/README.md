# Kannan–Vempala analysis

`Model/` is the compact audit surface: the program (`Pseudocode.lean`), the input and the
sampler contract (`ProblemSetting.lean`), and Theorem 2 for the program (`Theorem.lean`).
This directory contains the arguments behind it:

- `PseudocodeProof.lean` computes the output law: the program returns a lattice point `x`
  with probability `∫ prodTent (toState x) p dsampler(p)`.
- `TheoremProof.lean` turns that into the density form and applies Theorem 2.
- `AuditCheck.lean` checks the model closure and prints the axioms of the capstone.
- The rounding laws: `Tent.lean` (the tent function), `RoundLaw.lean` (the rounding law on
  `ℤⁿ`), `ProdKernel.lean` and `KernelIntegral.lean` (the product tent kernel and its
  integrals), `ContTent.lean` (the continuous tent law and its escape bound).
- The inflation and the escape bound: `Defs.lean` (`κ`, the loss, the choice of `c`),
  `Inflate.lean` (the inflated polytope and its volume), `SubgaussianTail.lean` and
  `Escape.lean` (the probability that rounding leaves the inflated polytope).
- `HitProbability.lean` proves Theorem 2 in density form, with the escape mass discharged.
- `SamplerRoutes.lean` connects the sampler contract to samplers the Markov-chain theory
  provides: total-variation mixing at tolerance `θ / V`, exact rejection, and the lazy
  ball walk.

## Deviations from the paper

Both are recorded where they arise, in `HitProbability.lean`:

- The sampler's density is assumed within `1 ± ε` of uniform **pointwise** on the inflated
  polytope, not merely in total variation.  The paper states a relative error, which a
  total-variation hypothesis does not give.
- The loss is `e^{−c²/2}`, not `2e^{−c²}`: the paper's inflation `κ = c + √(2 log r)`
  supports only the former.
