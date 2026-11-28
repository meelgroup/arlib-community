/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Kannan–Vempala lattice sampling

Sampling lattice points of a polytope by inflating it, sampling the inflated body
continuously, and rounding each coordinate at random ([KV97], Theorem 2).  Read `Model/` for
the compact audit surface — the program and the probability window for each lattice point —
and `Analysis/` for the rounding laws, the escape bound, and the proof.
-/

import ArlibCommunity.Algorithms.KV97.Model.Theorem
import ArlibCommunity.Algorithms.KV97.Analysis.AuditCheck
import ArlibCommunity.Algorithms.KV97.Analysis.SamplerRoutes
