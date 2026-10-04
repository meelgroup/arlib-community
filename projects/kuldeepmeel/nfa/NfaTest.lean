/-
# NfaTest

Tests that are not theorems: the planted breaches that make the build-time
checkers falsifiable. Kept out of `Nfa` so that the library a client
imports carries no deliberately-broken declarations.
-/

import NfaTest.CostSealBreaches
