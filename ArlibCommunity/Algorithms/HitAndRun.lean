/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Hit-and-run

A formalization of hit-and-run on a convex body given by a membership oracle: the
explicit sampler `Program.sampler`, charged through `Arlib.Computation` with one `query`
per membership call, its output law on a random tape, and its accuracy and query bound
(`hitAndRun_correct`, `hitAndRun_queries`), built on the direction/chord kernel, its
stationary uniform law, and an unconditional corrected mixing analysis based on
Lovász's 1999 paper [Lov99].  Read `Model/` for the compact audit surface and
`Analysis/` for proofs and supporting measure theory, convex geometry,
localization, conductance, and warm-start analysis.
-/

import ArlibCommunity.Algorithms.HitAndRun.Model.Theorem
import ArlibCommunity.Algorithms.HitAndRun.Analysis.KernelTheorem
import ArlibCommunity.Algorithms.HitAndRun.Analysis.AuditCheck
import ArlibCommunity.Algorithms.HitAndRun.Meta.Audit
