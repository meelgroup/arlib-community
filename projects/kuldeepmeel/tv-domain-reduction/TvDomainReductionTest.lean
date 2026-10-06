/-
# TvDomainReductionTest

Tests that are not theorems: the planted breaches that make the build-time
checkers falsifiable. Kept out of `TvDomainReduction` so that the library a client
imports carries no deliberately-broken declarations.

`#programSeal` refuses any namespace but the canonical `TvDomainReduction.Program`,
so each planted breach has to occupy that namespace alone — which makes the module
the unit of separation. `CostSealBreaches` keeps the cheats the compiler rejects on
its own; `Breach/*` is one `#programSeal` rejection each.
-/

import TvDomainReductionTest.CostSealBreaches
import TvDomainReductionTest.Breach.Exchange
import TvDomainReductionTest.Breach.Noncomputable
import TvDomainReductionTest.Breach.CasesOn
import TvDomainReductionTest.Breach.HandPriced
import TvDomainReductionTest.Breach.Cost
import TvDomainReductionTest.Breach.Transitive
import TvDomainReductionTest.Breach.Measure
import TvDomainReductionTest.Breach.PeakAt
