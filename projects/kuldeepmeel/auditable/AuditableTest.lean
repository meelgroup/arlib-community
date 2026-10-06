/-
# AuditableTest

Tests that are not theorems: the planted breaches that make the build-time
checkers falsifiable. Kept out of `Auditable` so that the library a client
imports carries no deliberately-broken declarations.
-/

import AuditableTest.CostSealBreaches
