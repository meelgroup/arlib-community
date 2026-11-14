/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Foundations.MarkovChainTheory.Prelude
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Gaussian walks: model vocabulary

The pieces of the Metropolis-filtered Gaussian ball walk and of the speedy Metropolis–Gaussian
walk: the Metropolis acceptance probability, the one-step density, the probability of moving,
and the `ℓ`-weighted Gaussian target of the speedy walk.
-/

open ArlibCommunity.Foundations.Convex

namespace ArlibCommunity.Foundations.MarkovChainTheory

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The **Metropolis acceptance probability** `min(1, g(y)/g(x))` for the Gaussian weight
`g(x) = e^{-‖x‖²/(2s)}`: the probability with which a proposal `y` made from `x` is
accepted, *given* that `y` lies in the body.  The indicator `1_K(y)` of the body is not
part of this definition; it enters in `metropolisGaussian`, where the proposal measure is
restricted to `K`. -/
noncomputable def metropolisAccept (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  min 1 (gaussianWeight s y / gaussianWeight s x)

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The **unnormalised one-step density** of the walk: `1[y ∈ x + δBₙ] · min(1, g(y)/g(x))`,
i.e. the acceptance probability restricted to the proposal ball.  Dividing by
`vol(δBₙ)` and multiplying by `1_K(y)` gives the density of the moving part of the kernel
with respect to Lebesgue measure. -/
noncomputable def metropolisDensity (s δ : ℝ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  (Metric.ball x δ).indicator (metropolisAccept s x) y

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The **probability that a step actually moves**,

    m(x) = vol(x + δBₙ)⁻¹ · ∫_{K ∩ (x + δBₙ)} min(1, g(y)/g(x)) dy,

i.e. the chance that the proposal lands in `K` *and* survives the acceptance test.  It is
the Metropolis analogue of the ball walk's local conductance `ArlibCommunity.Foundations.MarkovChainTheory.ell`,
to which it reduces when `g` is constant.  As with `ell`, `ℝ≥0∞` divides by zero to zero,
so `m(x) = 0` when the proposal ball is null. -/
noncomputable def metropolisMove (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  (∫⁻ y in K, metropolisDensity s δ x y) / volume (Metric.ball x δ)

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- **The probability that a step of the speedy Metropolis–Gaussian walk moves**,

    m(x) = (∫_{K} 1[y ∈ B(x,δ)]·min(1, g(y)/g(x)) dy) / vol(B(x,δ) ∩ K),

the mean acceptance probability over the accepted part `B(x,δ) ∩ K` of the proposal ball.

Contrast `ArlibCommunity.Foundations.MarkovChainTheory.metropolisMove`, whose denominator is `vol(B(x,δ))`: the speedy
proposal *conditions* on landing in `K`, so the normaliser is the volume of `B(x,δ) ∩ K`.  As
usual `ℝ≥0∞` divides by zero to zero, so `m(x) = 0` when `vol(B(x,δ) ∩ K) = 0` — the numerator
vanishes there too (`lintegral_metropolisDensity_le`), and the kernel below degenerates to
`dirac x`. -/
noncomputable def speedyMetropolisMove (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  (∫⁻ y in K, metropolisDensity s δ x y) / volume (Metric.ball x δ ∩ K)

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The **`ℓ·γ`-weighted measure** `1_K(x)·ℓ(x)·e^{−‖x‖²/(2s)} dx` — the unnormalised stationary
measure of the speedy Metropolis–Gaussian walk, and the density for which
`ArlibCommunity.Foundations.MarkovChainTheory.ellGaussian_isoperimetry_measurable_logTwo` (`ArlibCommunity/Foundations/Convex/GaussianIsoperimetry/Analysis/IsoWeighted.lean`) proves an
isoperimetric inequality.  A plain construction. -/
noncomputable def ellGaussianMeasure (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume.restrict K).withDensity (fun x => ell K δ x * gaussianWeight s x)

end

section
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {n : ℕ}

/-- The **`ℓ·γ`-weighted probability measure** on `K`: the stationary distribution of the speedy
Metropolis–Gaussian walk.  A plain construction; `isProbabilityMeasure_ellGaussianProb` gives the
guards under which it is a probability measure, and
`isProbabilityMeasure_ellGaussianProb_unitBall` discharges them on the witness. -/
noncomputable def ellGaussianProb (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (ellGaussianMeasure K δ s Set.univ)⁻¹ • ellGaussianMeasure K δ s

end

section
open MeasureTheory
variable {n : ℕ}

/-- **One step of the Metropolis-filtered Gaussian ball walk** at variance `s`: propose a uniform
point of the ball `B(x, δ)`, accept it if it lies in `K` with probability
`min(1, e^{-‖y‖²/(2s)} / e^{-‖x‖²/(2s)})`, and otherwise stay at `x`. -/
noncomputable def metropolisGaussianStep (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume (Metric.ball x δ))⁻¹ • (volume.restrict K).withDensity (metropolisDensity s δ x)
    + (1 - metropolisMove K δ s x) • Measure.dirac x

/-- **One step of the speedy Metropolis–Gaussian walk**: as the Metropolis walk, but proposing
a uniform point of `B(x, δ) ∩ K` rather than of `B(x, δ)`, so that no step is wasted leaving
the body. -/
noncomputable def speedyMetropolisGaussianStep (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume (Metric.ball x δ ∩ K))⁻¹ • (volume.restrict K).withDensity (metropolisDensity s δ x)
    + (1 - speedyMetropolisMove K δ s x) • Measure.dirac x

end

end ArlibCommunity.Foundations.MarkovChainTheory
