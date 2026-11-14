# Kannan–Vempala lattice-point sampling

**Paper.** Ravi Kannan, Santosh Vempala. *Sampling lattice points.* Proceedings
of the 29th Annual ACM Symposium on Theory of Computing (STOC), 1997,
pp. 696–700. Key `[KV97]` in `REFERENCES.md`.

## The problem

Sample a nearly uniform lattice point of a polytope
`P = {x ∈ ℝⁿ | ⟪Aᵢ, x⟫ ≤ bᵢ}`, using a sampler for continuous distributions. The
algorithm inflates `P` by a margin depending on a parameter `c` and on the number
of facets `r`, draws a point `p` of the inflated polytope from a nearly uniform
sampler, and rounds each coordinate of `p` at random to one of the two
neighbouring integers, with probabilities given by the tent function.

## What is proved

`latticePoint_probability` (`Model/Theorem.lean`), Theorem 2 of [KV97] for this
program. Let the sampler's density be within `1 ± ε` of uniform at every point of
the inflated polytope, with normaliser `V`. Then every lattice point of `P` is
returned with probability between

    (1 − ε)(1 − e^{−c²/2}) / V   and   (1 + ε) / V.

`Analysis/SamplerRoutes.lean` shows how to meet the sampler assumption with
samplers the Markov-chain theory provides: total-variation mixing, exact rejection,
and the lazy ball walk.

## Where it differs from the paper

- The sampler is assumed close to uniform **pointwise**, not only in total
  variation. The paper states a relative error, and a total-variation bound does
  not give one.
- The loss is `e^{−c²/2}`, not the paper's `2e^{−c²}`. The paper's inflation
  `κ = c + √(2 log r)` supports only the former.

Both are explained in `Analysis/HitProbability.lean`.

## How to read it

- `Model/` is the audit surface: `Prelude.lean` and `ProblemSetting.lean` (the
  input and the sampler assumption), `Pseudocode.lean` (the program and its
  output law) and `Theorem.lean`.
- `Analysis/README.md` is a guide to the proof files.
