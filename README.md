# arlib-community

Analyses of **specific randomised algorithms**, in Lean 4, built on top of
[arlib](https://github.com/meelgroup/arlib).

## The split with arlib

arlib is organised by *subject*: finite probability and concentration, Markov
chain mixing, information theory, knowledge compilation, communication
complexity — results stated without reference to any one algorithm. This
repository holds the other half: the analysis of a *named* algorithm, one
directory and one namespace per algorithm.

The dependency runs one way. arlib-community imports arlib; arlib never imports
anything here. That keeps arlib's build small and its area layering intact, and
it means an algorithm can be added here without touching the shared core.

What an entry must still meet is arlib's own rule: only the
**problem-independent** half of an algorithm's analysis belongs in a shared
library. The law of a counter, the arithmetic of a run-count schedule, a
termination argument — those are reusable. Exhibiting the structure the
algorithm needs for one particular counting or sampling problem is the using
project's obligation and stays there. *An entry that cannot be stated without
naming a problem is a sign the split has not been found yet.*

## What's inside

Three algorithm entries so far.

| Area | Contents | Start here |
| --- | --- | --- |
| `Algorithms/TPA` | Huber's Tootsie Pop Algorithm: its contraction-counter tail, Poisson law, almost-sure termination, and two-phase run-count schedule. | [ArlibCommunity/Algorithms/TPA.lean](ArlibCommunity/Algorithms/TPA.lean) |
| `Algorithms/HitAndRun` | Lovász's direction/chord sampler, finite-facet realization, stationarity, and a corrected unconditional mixing theorem. The compact statement surface is under `Model/`; proof background is under `Analysis/`. | [ArlibCommunity/Algorithms/HitAndRun.lean](ArlibCommunity/Algorithms/HitAndRun.lean) |
| `Algorithms/CV18` | Cousins--Vempala accelerated Gaussian cooling: an executable membership-oracle program and its discharged schedule, measure, sharp accelerated-moment, advertised-step average-conductance, product, and cost analysis. The remaining dependent walk/composition input is explicit; no unconditional capstone is asserted. | [ArlibCommunity/Algorithms/CV18.lean](ArlibCommunity/Algorithms/CV18.lean) |

`import ArlibCommunity` gives you everything; `import ArlibCommunity.Algorithms`
gives you one area; importing a single module gives you one piece. Every
declaration lives in the namespace matching its module path, and each algorithm
gets a namespace of its own (`ArlibCommunity.Algorithms.TPA`) — the entries are
independent, and short names like `tpaTail` would otherwise collide.

The area roots carry the real documentation: read the corresponding
`ArlibCommunity/Algorithms/<Name>.lean` before reading modules under it.

## Getting started

Use the same toolchain as arlib, which is Mathlib's own — today:

```
leanprover/lean4:v4.33.0
```

Copy that line into your `lean-toolchain`, then add arlib-community to your
`lakefile.toml`:

```toml
[[require]]
name = "arlib-community"
git = "https://github.com/meelgroup/arlib-community.git"
rev = "main"
```

arlib-community requires arlib, which requires Mathlib, so neither needs to be
required separately. Then:

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

Always run `lake exe cache get` first. Without it, Lake compiles Mathlib from
source, which takes hours.

### A worked example

```lean
import ArlibCommunity.Algorithms

open ArlibCommunity.Algorithms.TPA

-- A TPA run whose centre-to-shell measure ratio is `c` terminates almost surely:
-- the probability of performing more than `m` contractions tends to 0.
example {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun m => tpaTail m c) Filter.atTop (nhds 0) :=
  tendsto_tpaTail_atTop hc

-- And the counter's law is exactly Poisson(ln(1/c)).
example (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ((MeasureTheory.Measure.pi (fun _ : Fin m => unifUnit))
        {u : Fin m → ℝ | c < ∏ i, u i}).toReal
      - ((MeasureTheory.Measure.pi (fun _ : Fin (m + 1) => unifUnit))
        {u : Fin (m + 1) → ℝ | c < ∏ i, u i}).toReal
      = Arlib.Probability.poissonPMF (-Real.log c) m :=
  prob_exactly_eq_poissonPMF m hc hc1
```

`ArlibCommunityTest/` holds these as compiled examples; `lake test` runs them.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). In short: the house style is arlib's —
[CONVENTIONS.md](https://github.com/meelgroup/arlib/blob/main/CONVENTIONS.md)
governs naming, namespacing, statement shape and docstrings here too. Every
paper an entry formalizes goes in [REFERENCES.md](REFERENCES.md) with the short
key its docstrings cite.

The invariant is the same as arlib's and CI enforces it: no `sorry`, and no
axiom beyond the three Mathlib itself uses (`propext`, `Classical.choice`,
`Quot.sound`).

## Versioning and stability

Pre-1.0; there is no stable API. It tracks arlib, which is itself pre-1.0 and
renames as it consolidates. If you depend on this, pin a specific commit.

## License

Released under the [Apache License 2.0](LICENSE), following Mathlib.

Copyright © 2026 the arlib contributors. The per-file headers are authoritative
for who holds copyright in which module.

## Origins

The `Algorithms` area started life inside arlib and moved here in 2026, when the
two halves were separated: subject-organised infrastructure in arlib,
algorithm-by-algorithm analyses in arlib-community.

## Acknowledgements

Built with the assistance of **Claude** (Anthropic's Claude Code).
