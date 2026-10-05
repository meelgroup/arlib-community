/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `ArlibCommunity.Algorithms` — analyses of specific algorithms

Randomised algorithms and estimators, each with the part of its analysis that is
independent of the problem it is applied to.

The area's organising principle is the split every entry here makes. An
algorithm's analysis divides into a *generic* half — the law of a counter, the
arithmetic of a run-count schedule, a termination argument — and a
*problem-specific* half — exhibiting the structure the algorithm needs for one
particular counting or sampling problem. Only the generic half belongs here; the
problem-specific half stays in the project that uses it. An entry that cannot be
stated without naming a problem is a sign the split has not been found yet.

Each algorithm gets its own directory *and* its own namespace
`ArlibCommunity.Algorithms.<Name>` — the entries are independent of one another,
and their names (`tpaTail`, and whatever follows) would otherwise collide.

## Sub-areas

* `ArlibCommunity.Algorithms.TPA` — the Tootsie Pop Algorithm (Huber; the
  sub-area root records that which of his papers it follows is unresolved): the
  Poisson law of its contraction counter, almost-sure termination, and the
  two-phase run-count schedule.
* `ArlibCommunity.Algorithms.HitAndRun` — the hit-and-run sampler: its
  direction/chord kernel, a finite-facet realization, stationarity, and a fully
  discharged corrected mixing theorem.
* `ArlibCommunity.Algorithms.CV18` — Cousins--Vempala accelerated Gaussian
  cooling: the executable oracle program and discharged analysis, with the two
  remaining quantitative inputs exposed as hypotheses.
-/

import ArlibCommunity.Algorithms.TPA
import ArlibCommunity.Algorithms.HitAndRun
import ArlibCommunity.Algorithms.CV18
