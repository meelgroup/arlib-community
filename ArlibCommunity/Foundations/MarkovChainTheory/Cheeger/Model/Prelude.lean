/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.Prelude
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Cheeger's inequality: model vocabulary

The `L²` quantities of a Markov kernel: the Dirichlet form, the variance, the Rayleigh quotient
over non-constant square-integrable functions, and the spectral gap as the infimum of Rayleigh
quotients.  The spectral gap is defined variationally; no eigenvalues appear.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.MarkovChainTheory

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **real Dirichlet form** of `f`:

`E(f, f) = (1/2) ∫∫ (f x − f y)² dP_x(y) dpi(x)`.

This is the `ℝ`-valued counterpart of `ArlibCommunity.Foundations.MarkovChainTheory.dirichletForm`.  The `ℝ≥0∞`
version needs no integrability hypotheses but cannot be paired with a variance; this one
can, at the price of carrying `MemLp f 2 pi` wherever the value matters.  Note that the
definition itself is total: for a non-integrable `f` the Bochner integral is `0` by
convention, so every lemma below that has content states its integrability hypothesis
explicitly. -/
noncomputable def dirichletFormReal (P : Kernel Ω Ω) (pi : Measure Ω) (f : Ω → ℝ) : ℝ :=
  (∫ x, ∫ y, (f x - f y) ^ 2 ∂(P x) ∂pi) / 2

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **variance** of `f` under `pi`, `∫ f² dpi − (∫ f dpi)²`.  This is exactly
`ProbabilityTheory.variance f pi`; see `varianceReal_eq_variance` and `varianceReal_eq_sub`. -/
noncomputable def varianceReal (pi : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ProbabilityTheory.variance f pi

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The functions the spectral-gap infimum ranges over: those in `L²(pi)` whose variance
does not vanish.  The variance condition is what keeps the Rayleigh quotient from being the
junk value `x / 0 = 0`, and by `varianceReal_eq_zero_iff` it excludes exactly the a.e.
constant functions — on which the Dirichlet form vanishes too, so `0/0` would otherwise
force `spectralGap = 0` on every chain. -/
def AdmissibleL2 (pi : Measure Ω) : Set (Ω → ℝ) :=
  {f : Ω → ℝ | MemLp f 2 pi ∧ varianceReal pi f ≠ 0}

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **Rayleigh quotient** `E(f, f) / Var(f)` of the chain at `f`. -/
noncomputable def rayleighQuotient (P : Kernel Ω Ω) (pi : Measure Ω) (f : Ω → ℝ) : ℝ :=
  dirichletFormReal P pi f / varianceReal pi f

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The set of values of the Rayleigh quotient on the admissible functions. -/
noncomputable def rayleighSet (P : Kernel Ω Ω) (pi : Measure Ω) : Set ℝ :=
  rayleighQuotient P pi '' AdmissibleL2 pi

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **spectral gap** of a reversible chain: the infimum of the Rayleigh quotient
`E(f,f) / Var(f)` over `f ∈ L²(pi)` of nonzero variance.

See the module docstring for why this is `sInf` of an image rather than the more idiomatic
`⨅ f ∈ _, _`: over `ℝ` the latter collapses to `0`. -/
noncomputable def spectralGap (P : Kernel Ω Ω) (pi : Measure Ω) : ℝ :=
  sInf (rayleighSet P pi)

end

end ArlibCommunity.Foundations.MarkovChainTheory
