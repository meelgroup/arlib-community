/-
# Esa22CopyTest

Tests that are not theorems: the planted breaches that make the build-time
checkers falsifiable. Kept out of `Esa22Copy` so that the library a client
imports carries no deliberately-broken declarations.
-/

import Esa22CopyTest.CostSealBreaches
import Esa22CopyTest.Breach.Exchange
import Esa22CopyTest.Breach.Noncomputable
import Esa22CopyTest.Breach.CasesOn
import Esa22CopyTest.Breach.HandPriced
import Esa22CopyTest.Breach.Cost
import Esa22CopyTest.Breach.Transitive
import Esa22CopyTest.Breach.Measure
import Esa22CopyTest.Breach.PeakAt
