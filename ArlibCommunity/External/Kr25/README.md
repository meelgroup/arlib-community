# Vendored kr-25 proof material

This directory contains the five additional Lean modules needed by the CV18
sharp accelerated-moment proof. The shared 68-module localization foundation
already maintained by the active HitAndRun development is reused rather than
duplicated. The five additions were copied from the local
`kr-25-ssm/lean` snapshot at commit
`56da0f89460922764785e3c61664bcb00ca9a77f` and migrated from Lean 4.32 to
Lean 4.33.

Imports between copied modules were rewritten to the
`ArlibCommunity.External.Kr25` module path. The active build has no filesystem
or Lake dependency on the source snapshot.
