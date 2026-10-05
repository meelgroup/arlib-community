/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# ArlibCommunity

Analyses of *specific* randomised algorithms, built on top of
[arlib](https://github.com/meelgroup/arlib).

The two repositories divide as follows. **arlib** holds the general,
subject-organised infrastructure — finite probability, concentration, Markov
chains, information theory, knowledge compilation — the results that are stated
without reference to any one algorithm. **arlib-community** holds the other
half: the analysis of a named algorithm, one directory per algorithm, in a
namespace of its own. An entry here may freely import arlib; arlib never depends
on anything here, so the split also keeps arlib's build small and its area
layering intact.

The rule an entry must still meet is arlib's: only the *problem-independent*
half of an algorithm's analysis belongs in a shared library. The law of a
counter, the arithmetic of a run-count schedule, a termination argument — those
are reusable. Exhibiting the structure the algorithm needs for one particular
counting or sampling problem is the using project's obligation, and stays in the
using project.

Importing `ArlibCommunity` pulls in everything. Import an area
(`import ArlibCommunity.Algorithms`) for one subject, or a single module for one
piece. Every declaration lives in the namespace matching its module path.

## Areas

* `ArlibCommunity.Algorithms` — analyses of specific algorithms, including TPA,
  hit-and-run, and the currently discharged portion of CV18 accelerated
  Gaussian cooling.
-/

import ArlibCommunity.Algorithms
