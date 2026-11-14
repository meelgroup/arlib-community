/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.Cheeger.Model.Prelude
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Mixing from conductance: model vocabulary

The `L²` pairing `⟨f, P f⟩` and nonnegativity of the spectrum, which is what laziness buys.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.MarkovChainTheory

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **Dirichlet pairing** `⟪f, g⟫_P = ∫∫ f(x) g(y) d(pi ⊗ₘ P)(x,y)`, i.e.
`∫ f · (T g) dpi` (`pairing_eq_integral_mul_markovOp`). -/
noncomputable def pairing (P : Kernel Ω Ω) (pi : Measure Ω) (f g : Ω → ℝ) : ℝ :=
  ∫ p, f p.1 * g p.2 ∂(pi ⊗ₘ P)

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Markov operator is positive semidefinite**: `∫ f · (T f) dpi ≥ 0` for every
`f ∈ L²(pi)`.  For a lazy chain `P = (I + Q)/2` this holds because
`⟪f, P f⟫ = (‖f‖² + ⟪f, Q f⟫)/2 ≥ 0`.

This is a property of the *kernel* — it says nothing about conductance, spectral gap, or
mixing — and is the hypothesis under which the spectral gap gives a per-step `L²`
contraction. -/
def HasNonnegSpectrum (P : Kernel Ω Ω) (pi : Measure Ω) : Prop :=
  ∀ f : Ω → ℝ, Measurable f → MemLp f 2 pi → 0 ≤ pairing P pi f f

end

end ArlibCommunity.Foundations.MarkovChainTheory
