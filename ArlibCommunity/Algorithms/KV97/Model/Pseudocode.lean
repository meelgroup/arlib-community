/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.KV97.Model.Prelude
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Kannan–Vempala pseudocode

```
input:  polytope P = {x | Ax ≤ b}, parameters c, r
1. P' ← inflate every facet of P by κ‖Aᵢ‖, κ = c + √(2 log r)
2. p  ← a sample from a near-uniform sampler on P'
3. z  ← round each coordinate of p independently:
          zᵢ = ⌊pᵢ⌋ + 1 with probability pᵢ − ⌊pᵢ⌋, and zᵢ = ⌊pᵢ⌋ otherwise
4. return z
```

`output sampler` is the law of `z`.  Step 1 is `Problem.inflatedBody`
(`ProblemSetting.lean`); step 2 is the sampler, a parameter of the program whose contract
is `AlmostUniformSampler`.  The caller keeps `z` only if `z ∈ P` (rejection); the theorem
is about the probability of each lattice point of `P` before that test.
-/

namespace ArlibCommunity.Algorithms.KV97

open MeasureTheory

variable {n : ℕ}

/-- **The one-dimensional rounding law**: `⌊a⌋ + Bernoulli(a − ⌊a⌋)`, presented as
the tent density against counting measure on `ℤ`. -/
noncomputable def tentInt (a : ℝ) : Measure ℤ :=
  (Measure.count : Measure ℤ).withDensity (fun m => ENNReal.ofReal (tent (a - m)))

/-- **The rounding law on `ℤⁿ`** for a fixed `p`: independent coordinates, each a
one-dimensional rounding law. -/
noncomputable def roundLaw (p : Fin n → ℝ) : Measure (Fin n → ℤ) :=
  Measure.pi (fun i => tentInt (p i))

/-- Step 3: randomized rounding of a point of `ℝⁿ` to `ℤⁿ`, coordinate by coordinate. -/
noncomputable def round (p : State n) : Measure (LatticePoint n) :=
  roundLaw (fun i => p i)

/-- **The program**: draw `p` from the sampler and round it.  The law of the returned
lattice point. -/
noncomputable def output (sampler : Measure (State n)) : Measure (LatticePoint n) :=
  sampler.bind round

end ArlibCommunity.Algorithms.KV97
