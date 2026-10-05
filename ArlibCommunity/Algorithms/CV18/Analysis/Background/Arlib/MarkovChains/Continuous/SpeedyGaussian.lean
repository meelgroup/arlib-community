/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyWalk
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisGaussian

/-!
# The speedy walk with a Gaussian Metropolis filter

Two mixing chains already exist in this repository and neither is stationary for the density
Cousins–Vempala's volume phases actually sample:

* `Arlib.MarkovChains.metropolisGaussian` (`MetropolisGaussian.lean:444`) is reversible for
  `1_K·γ` — the Gaussian-restricted density, but *unfiltered by the local conductance*, so its
  conductance argument needs a pointwise floor on `ℓ` that
  `Arlib/MarkovChains/Continuous/EllFloor.lean` shows is unsatisfiable on the cube.
* `Arlib.MarkovChains.speedyWalk` (`SpeedyWalk.lean:186`) is reversible for `1_K·ℓ` — the
  *speedy* device that removes the `ℓ`-floor, but the target is Lebesgue-flat, not
  Gaussian-tilted.

This file builds the hybrid and proves it is a Markov kernel reversible for `1_K·ℓ·γ`, the
density for which `Arlib.ellGaussian_isoperimetry_measurable_logTwo`
(`Arlib/Convexity/IsoWeighted.lean`) proves an isoperimetric inequality with merely measurable
partitions.  `IsoWeighted.lean`'s module docstring assessed the construction and declined to
build it ("it would need a `def`, which is out of scope here"); this file carries it out and
confirms the assessment's algebra.

## The construction

From `x`, propose `y` uniformly from `B(x, δ) ∩ K` — the **speedy** proposal — then accept with
the Gaussian Metropolis probability `min(1, g(y)/g(x))`, `g(x) = e^{−‖x‖²/(2s)}`; otherwise stay
at `x`.  The move density is

    q(x,y) = (vol(B(x,δ) ∩ K))⁻¹ · 1_{B(x,δ)∩K}(y) · min(1, g(y)/g(x))
           = (ℓ(x)·vol(δBₙ))⁻¹ · 1_{B(x,δ)∩K}(y) · min(1, g(y)/g(x)),

the two forms agreeing because `ℓ(x)·vol(δBₙ) = vol(B(x,δ) ∩ K)` by `volume_ball_eq`.  Against
the target density `π(x) = 1_K(x)·ℓ(x)·g(x)` this gives

    π(x)·q(x,y) = vol(δBₙ)⁻¹ · 1_K(x)·1_K(y)·1_{B(x,δ)}(y) · min(g x, g y),

visibly symmetric in `(x, y)`.  **The algebra is exactly as `IsoWeighted.lean` predicted**: the
`1/ℓ(x)` normaliser of the speedy proposal cancels the `ℓ(x)` of the target — the cancellation
`Arlib.MarkovChains.ell_mul_speedyWalk` performs, here isolated as
`ell_mul_inv_volume_inter_ball` — and the filter symmetrises `g` exactly as
`gaussianWeight_mul_metropolisDensity_comm` does.

## Why the name is not `speedyGaussian`

`Arlib.MarkovChains.conductance_speedyGaussian_ge` (`SpeedyConductanceSharp.lean:320`) already
exists and is **not** a theorem about the kernel built here: it is abstract in its kernel `P`,
and its two corollaries (`SpeedyOverlap.lean:742`, `OverlapSqrt.lean:669`) instantiate it at
`Arlib.MarkovChains.speedyWalk`.  A `def speedyGaussian` in this namespace would make that
theorem read as a conductance bound for this kernel, which it is not.  Hence
`speedyMetropolisGaussian` — speedy proposal, Metropolis–Gaussian filter.

## Main definitions

* `Arlib.MarkovChains.speedyMetropolisMove K δ s x` — the probability that a step moves,
  `(∫_{K} 1[y ∈ B(x,δ)]·min(1, g(y)/g(x)) dy) / vol(B(x,δ) ∩ K)`, i.e. the **mean acceptance
  over `B(x,δ) ∩ K`**.  This is *not* `metropolisMove`: the denominator is the volume of the
  accepted part of the proposal ball, not of the whole ball.
* `Arlib.MarkovChains.speedyMetropolisGaussian K δ s` — the kernel, `speedyMetropolisGaussianAux`
  on a measurable `K` and the identity kernel otherwise (the `dif` is forced: the normaliser
  `x ↦ vol(B(x,δ) ∩ K)⁻¹` is measurable only via `measurable_volume_inter_ball`, which needs
  `MeasurableSet K`; `metropolisGaussian` avoids the `dif` because its normaliser is constant).
* `Arlib.MarkovChains.ellGaussianMeasure K δ s` — the unnormalised target
  `(volume.restrict K).withDensity (ℓ·g)`, and `ellGaussianProb K δ s` its normalisation.

## Main results

* `Arlib.MarkovChains.speedyMetropolisMove_le_one` — **the new `≤ 1` lemma**, and it is genuinely
  new: neither `metropolisMove_le_one` (whose denominator is the larger `vol(B(x,δ))`) nor the
  speedy walk's own Markov proof (whose numerator is the *whole* accepted volume, with no filter)
  applies verbatim.  Its content is `∫_A 1[y ∈ B(x,δ)]·a(x,y) dy ≤ vol(B(x,δ) ∩ A)`
  (`lintegral_metropolisDensity_le`), the acceptance probability being at most `1`.
* `Arlib.MarkovChains.isMarkovKernel_speedyMetropolisGaussian`.
* `Arlib.MarkovChains.ellGaussian_mul_speedyMetropolisGaussian` — **the crux**: the pointwise
  identity `ℓ(x)·g(x)·P_x(T) = vol(δBₙ)⁻¹·∫_{T∩K} g(x)·p(x,y) dy + 1_T(x)·ℓ(x)·g(x)·(1 − m(x))`.
* `Arlib.MarkovChains.isReversible_speedyMetropolisGaussian`,
  `Arlib.MarkovChains.isReversible_speedyMetropolisGaussian_prob`,
  `Arlib.MarkovChains.invariant_speedyMetropolisGaussian` — **detailed balance for `1_K·ℓ·γ`**,
  and hence its invariance.  No convexity of `K`, no positivity of `δ` or `s`.
* `Arlib.MarkovChains.exists_speedyMetropolisGaussian_witness` — the non-vacuity witness.

## The `StuckPoints` guard is subsumed, deliberately

`speedyWalk` carries an explicit `(StuckPoints K δ).indicator 1 x • dirac x` holding atom because
its move mass is exactly `1` off the stuck points, so a `1 − m(x)` atom would be identically zero
there and would have to be re-introduced by hand at `ell = 0`.  Here the filter makes the move
mass `< 1` in general, so the `metropolisGaussian`-style atom `(1 − m(x)) • dirac x` is needed
anyway — and it **subsumes** the guard: at a stuck `x` the numerator of `m(x)` is `0`
(`lintegral_metropolisDensity_le` with `vol(B(x,δ) ∩ K) = 0`), so `m(x) = 0` and the atom carries
all the mass, while the moving part is `⊤ • (zero measure) = 0`.  Correspondingly the crux needs
no `ell_mul_stuck_indicator`: the holding term is killed in the flow not by the indicator but by
the symmetry of its domain `T ∩ (S ∩ K)`.

## Scope: what is deliberately absent

A kernel, its Markov property and its reversibility.  **There is no conductance bound, no mixing
bound, no spectral-gap bound and no runtime statement here, in any form** — not as a theorem, not
as an assumed predicate, not as a `def` whose name asserts one — and nothing here makes anything
polynomial-time.  The only `def`s are `speedyMetropolisMove`, `speedyMetropolisGaussianAux`,
`speedyMetropolisGaussian`, `ellGaussianMeasure` and `ellGaussianProb`, all plain constructions,
and every property their names promise is proved below.

Section 7 at the end of the file — prose in a section comment, containing no declaration — sets
out what is still missing between this kernel and a conductance bound.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The probability of moving -/

/-- **The probability that a step of the speedy Metropolis–Gaussian walk moves**,

    m(x) = (∫_{K} 1[y ∈ B(x,δ)]·min(1, g(y)/g(x)) dy) / vol(B(x,δ) ∩ K),

the mean acceptance probability over the accepted part `B(x,δ) ∩ K` of the proposal ball.

Contrast `Arlib.MarkovChains.metropolisMove`, whose denominator is `vol(B(x,δ))`: the speedy
proposal *conditions* on landing in `K`, so the normaliser is the volume of `B(x,δ) ∩ K`.  As
usual `ℝ≥0∞` divides by zero to zero, so `m(x) = 0` when `vol(B(x,δ) ∩ K) = 0` — the numerator
vanishes there too (`lintegral_metropolisDensity_le`), and the kernel below degenerates to
`dirac x`. -/
noncomputable def speedyMetropolisMove (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  (∫⁻ y in K, metropolisDensity s δ x y) / volume (Metric.ball x δ ∩ K)

theorem speedyMetropolisMove_apply (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    speedyMetropolisMove K δ s x
      = (∫⁻ y in K, metropolisDensity s δ x y) / volume (Metric.ball x δ ∩ K) := rfl

/-- **The accepted mass over any set is at most the volume the set shares with the proposal
ball.**  The acceptance probability is at most `1` and the density vanishes off `B(x,δ)`, so
`∫_A p(x,y) dy ≤ vol(B(x,δ) ∩ A)`.

This one lemma does two jobs: at `A = K` it is the numerator bound that makes
`speedyMetropolisMove_le_one` true, and at `A = T ∩ K` it is the hypothesis of the crux
`ell_mul_inv_volume_inter_ball`.  It is strictly sharper than the bound
`metropolisMove_le_one` uses, which throws `K` away and stops at `vol(B(x,δ))`. -/
theorem lintegral_metropolisDensity_le (A : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ y in A, metropolisDensity s δ x y ≤ volume (Metric.ball x δ ∩ A) := by
  calc ∫⁻ y in A, metropolisDensity s δ x y
      ≤ ∫⁻ y in A, (Metric.ball x δ).indicator 1 y :=
        lintegral_mono fun y => metropolisDensity_le_indicator s δ x y
    _ = volume (Metric.ball x δ ∩ A) := by
        rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball]
        simp

/-- **The probability of moving is a probability.**  This is the `≤ 1` lemma the hybrid needs and
that neither parent supplies: `metropolisMove_le_one` divides by the *whole* ball, and the speedy
walk's Markov proof has no filter to bound.  Here the numerator is bounded by
`lintegral_metropolisDensity_le` against exactly the denominator `vol(B(x,δ) ∩ K)`. -/
theorem speedyMetropolisMove_le_one (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : speedyMetropolisMove K δ s x ≤ 1 := by
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact lintegral_metropolisDensity_le K δ s x

/-- **The probability of moving is a measurable function of the current point.**  The numerator is
`measurable_setLIntegral_metropolisDensity`; the denominator, unlike `metropolisMove`'s, is *not*
constant, and its measurability is `measurable_volume_inter_ball` — which is where
`MeasurableSet K` first becomes unavoidable. -/
theorem measurable_speedyMetropolisMove {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) : Measurable (speedyMetropolisMove K δ s) := by
  have hden : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      volume (Metric.ball x δ ∩ K) := by
    simpa [Set.inter_comm] using measurable_volume_inter_ball hK δ
  have h : speedyMetropolisMove K δ s = fun x =>
      (∫⁻ y in K, metropolisDensity s δ x y) * (volume (Metric.ball x δ ∩ K))⁻¹ := by
    funext x
    rw [speedyMetropolisMove_apply, div_eq_mul_inv]
  rw [h]
  exact (measurable_setLIntegral_metropolisDensity s δ K).mul hden.inv

/-! ## 2. The kernel -/

/-- **The speedy Metropolis–Gaussian walk on a measurable `K`.**  From `x`, the measure

    (vol(B(x,δ) ∩ K))⁻¹ • (volume.restrict K).withDensity (p(x, ·))  +  (1 − m(x)) • dirac x

with `p(x,y) = 1[y ∈ B(x,δ)]·min(1, g(y)/g(x))` (`metropolisDensity`) and `m(x)` the total
probability of moving (`speedyMetropolisMove`).  `speedyMetropolisGaussian` is the version that
does not carry the measurability proof; use that one. -/
noncomputable def speedyMetropolisGaussianAux (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun x := (volume (Metric.ball x δ ∩ K))⁻¹ •
        (volume.restrict K).withDensity (metropolisDensity s δ x)
      + (1 - speedyMetropolisMove K δ s x) • Measure.dirac x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have hden : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
        (volume (Metric.ball x δ ∩ K))⁻¹ := by
      have h : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          volume (Metric.ball x δ ∩ K) := by
        simpa [Set.inter_comm] using measurable_volume_inter_ball hK δ
      exact h.inv
    have hrw : ∀ x : EuclideanSpace ℝ (Fin n),
        ((volume (Metric.ball x δ ∩ K))⁻¹ •
              (volume.restrict K).withDensity (metropolisDensity s δ x)
            + (1 - speedyMetropolisMove K δ s x) • Measure.dirac x) t
          = (volume (Metric.ball x δ ∩ K))⁻¹ * (∫⁻ y in t ∩ K, metropolisDensity s δ x y)
            + (1 - speedyMetropolisMove K δ s x) * t.indicator 1 x := by
      intro x
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
        withDensity_apply _ ht, Measure.restrict_restrict ht, Measure.dirac_apply' _ ht]
    simp_rw [hrw]
    exact (hden.mul (measurable_setLIntegral_metropolisDensity s δ (t ∩ K))).add
      ((measurable_const.sub (measurable_speedyMetropolisMove hK δ s)).mul
        (measurable_one.indicator ht))

/-- Unfolding lemma for `speedyMetropolisGaussianAux`. -/
theorem speedyMetropolisGaussianAux_apply (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    speedyMetropolisGaussianAux K hK δ s x
      = (volume (Metric.ball x δ ∩ K))⁻¹ •
          (volume.restrict K).withDensity (metropolisDensity s δ x)
        + (1 - speedyMetropolisMove K δ s x) • Measure.dirac x := rfl

open scoped Classical in
/-- **The speedy walk with `δ`-steps on `K`, Metropolis-filtered for the Gaussian weight
`g(x) = e^{−‖x‖²/(2s)}`.**  From `x`: resample uniformly from `x + δBₙ` until the sample lands in
`K`; then accept the resulting `y` with probability `min(1, g(y)/g(x))`, and otherwise stay at
`x`.

Defined as `speedyMetropolisGaussianAux` when `K` is measurable and as the identity kernel
otherwise, so that it is a function of `K`, `δ` and `s` alone; every statement about its *value*
assumes `MeasurableSet K`. -/
noncomputable def speedyMetropolisGaussian (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  if hK : MeasurableSet K then speedyMetropolisGaussianAux K hK δ s
  else Kernel.deterministic id measurable_id

open scoped Classical in
/-- On a measurable `K`, `speedyMetropolisGaussian` is `speedyMetropolisGaussianAux`. -/
theorem speedyMetropolisGaussian_eq {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ s : ℝ) : speedyMetropolisGaussian K δ s = speedyMetropolisGaussianAux K hK δ s := dif_pos hK

/-- **The value of the kernel on a measurable event.**  The mass splits into the moving part
`vol(B(x,δ) ∩ K)⁻¹ ∫_{t ∩ K} p(x,y) dy` and the stay-put part `(1 − m(x))·1[x ∈ t]`. -/
theorem speedyMetropolisGaussian_apply_set {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n))
    {t : Set (EuclideanSpace ℝ (Fin n))} (ht : MeasurableSet t) :
    speedyMetropolisGaussian K δ s x t
      = (volume (Metric.ball x δ ∩ K))⁻¹ * (∫⁻ y in t ∩ K, metropolisDensity s δ x y)
        + (1 - speedyMetropolisMove K δ s x) * t.indicator 1 x := by
  rw [speedyMetropolisGaussian_eq hK, speedyMetropolisGaussianAux_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, withDensity_apply _ ht,
    Measure.restrict_restrict ht, Measure.dirac_apply' _ ht]

/-- **The speedy Metropolis–Gaussian walk is a Markov kernel**, for every `K`, `δ` and `s`.  Its
total mass is `m(x) + (1 − m(x))`, which is `1` because `speedyMetropolisMove_le_one` makes the
truncated subtraction exact.  Where the proposal can never be accepted the numerator of `m(x)`
vanishes, `m(x) = 0`, and the holding atom carries everything. -/
instance isMarkovKernel_speedyMetropolisGaussianAux (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (δ s : ℝ) : IsMarkovKernel (speedyMetropolisGaussianAux K hK δ s) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have h := speedyMetropolisGaussian_apply_set hK δ s x
    (MeasurableSet.univ (α := EuclideanSpace ℝ (Fin n)))
  rw [speedyMetropolisGaussian_eq hK] at h
  rw [h, Set.univ_inter, Set.indicator_of_mem (Set.mem_univ x), Pi.one_apply, mul_one,
    ← ENNReal.div_eq_inv_mul, ← speedyMetropolisMove_apply]
  exact add_tsub_cancel_of_le (speedyMetropolisMove_le_one K δ s x)

open scoped Classical in
instance isMarkovKernel_speedyMetropolisGaussian (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    IsMarkovKernel (speedyMetropolisGaussian K δ s) := by
  unfold speedyMetropolisGaussian
  split_ifs with hK
  · exact isMarkovKernel_speedyMetropolisGaussianAux K hK δ s
  · infer_instance

/-! ## 3. The `ℓ·γ`-weighted measure and the crux identity -/

/-- The **`ℓ·γ`-weighted measure** `1_K(x)·ℓ(x)·e^{−‖x‖²/(2s)} dx` — the unnormalised stationary
measure of the speedy Metropolis–Gaussian walk, and the density for which
`Arlib.ellGaussian_isoperimetry_measurable_logTwo` (`Arlib/Convexity/IsoWeighted.lean`) proves an
isoperimetric inequality.  A plain construction. -/
noncomputable def ellGaussianMeasure (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume.restrict K).withDensity (fun x => ell K δ x * gaussianWeight s x)

/-- The density of `ellGaussianMeasure` is measurable. -/
theorem measurable_ell_mul_gaussianWeight {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => ell K δ x * gaussianWeight s x :=
  (measurable_ell hK δ).mul (measurable_gaussianWeight s)

/-- The total weight of `K`, `∫_K ℓ·g`. -/
theorem ellGaussianMeasure_univ (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    ellGaussianMeasure K δ s Set.univ = ∫⁻ x in K, ell K δ x * gaussianWeight s x := by
  rw [ellGaussianMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- **The `ℓ·γ`-weighted measure lives on `K`.** -/
theorem ellGaussianMeasure_compl_eq_zero {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) : ellGaussianMeasure K δ s Kᶜ = 0 := by
  rw [ellGaussianMeasure, withDensity_apply _ hK.compl, Measure.restrict_restrict hK.compl,
    Set.inter_comm, Set.inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]

/-- **The `ℓ·γ`-weighted measure is absolutely continuous for Lebesgue measure.** -/
theorem ellGaussianMeasure_absolutelyContinuous (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    ellGaussianMeasure K δ s ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- **The total weight is finite** for `s > 0`: both `ℓ ≤ 1` and `g ≤ 1`, so `∫_K ℓ·g ≤ vol(K)`. -/
theorem ellGaussianMeasure_univ_le {s : ℝ} (hs : 0 < s) (K : Set (EuclideanSpace ℝ (Fin n)))
    (δ : ℝ) : ellGaussianMeasure K δ s Set.univ ≤ volume K := by
  rw [ellGaussianMeasure_univ]
  calc ∫⁻ x in K, ell K δ x * gaussianWeight s x ≤ ∫⁻ _ in K, (1 : ℝ≥0∞) :=
        lintegral_mono fun x => by
          calc ell K δ x * gaussianWeight s x ≤ 1 * 1 :=
                mul_le_mul' (ell_le_one K δ x) (gaussianWeight_le_one hs x)
            _ = 1 := one_mul 1
    _ = volume K := by rw [setLIntegral_one]

/-- **Set integrals against the `ℓ·γ`-weight.** -/
theorem setLIntegral_ellGaussianMeasure {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in S, g x ∂(ellGaussianMeasure K δ s)
      = ∫⁻ x in S ∩ K, ell K δ x * gaussianWeight s x * g x := by
  rw [ellGaussianMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _
    (measurable_ell_mul_gaussianWeight hK δ s) hg hS, Measure.restrict_restrict hS]
  rfl

/-- **The cancellation at the heart of the speedy device**, isolated:

    ℓ(x) · (vol(B(x,δ) ∩ K)⁻¹ · c)  =  vol(δBₙ)⁻¹ · c

for every `c ≤ vol(B(x,δ) ∩ K)`.  The `ℓ(x)` supplied by the stationary weight cancels exactly
the `vol(B(x,δ) ∩ K)` in the denominator of the speedy proposal, leaving the *constant*
normaliser of the plain ball walk.  This is `Arlib.MarkovChains.ell_mul_speedyWalk`'s algebra
extracted from its statement so that the Metropolis numerator can be substituted for `c`.

The hypothesis `hc` is exactly what makes the degenerate branch true rather than false: when
`vol(B(x,δ) ∩ K) = 0` the left side is `0 · ⊤ · c = 0` while the right side is `vol(δBₙ)⁻¹ · c`,
and only `c = 0` reconciles them. -/
theorem ell_mul_inv_volume_inter_ball (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {c : ℝ≥0∞} (hc : c ≤ volume (Metric.ball x δ ∩ K)) :
    ell K δ x * ((volume (Metric.ball x δ ∩ K))⁻¹ * c)
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ * c := by
  have hb : volume (Metric.ball x δ) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) :=
    volume_ball_eq x δ
  rcases eq_or_ne (volume (Metric.ball x δ ∩ K)) 0 with h0 | h0
  · have hc0 : c = 0 := le_antisymm (h0 ▸ hc) zero_le
    rw [hc0, mul_zero, mul_zero, mul_zero]
  · have hatop : volume (Metric.ball x δ ∩ K) ≠ ⊤ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left)
    calc ell K δ x * ((volume (Metric.ball x δ ∩ K))⁻¹ * c)
        = (volume (Metric.ball x δ ∩ K) * (volume (Metric.ball x δ ∩ K))⁻¹) *
            ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ * c) := by
          rw [ell_apply, hb, div_eq_mul_inv]; ring
      _ = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ * c := by
          rw [ENNReal.mul_inv_cancel h0 hatop, one_mul]

/-- **The crux identity.**  For every `x` and every measurable `T`,

    ℓ(x)·g(x)·P_x(T)
      = vol(δBₙ)⁻¹ · ∫_{T ∩ K} g(x)·p(x,y) dy  +  1_T(x)·ℓ(x)·g(x)·(1 − m(x)),

where `P` is the speedy Metropolis–Gaussian walk and `p = metropolisDensity`.  Two cancellations
happen here and they are independent: `ell_mul_inv_volume_inter_ball` turns the speedy
normaliser into the constant `vol(δBₙ)⁻¹`, and pulling `g(x)` under the integral sets up
`gaussianWeight_mul_metropolisDensity_comm`, which symmetrises the filter.

No hypothesis on `δ`, `s` or `vol(K)` is needed: at a point where the proposal is never accepted
the numerator vanishes, and `ell_mul_inv_volume_inter_ball`'s degenerate branch applies. -/
theorem ellGaussian_mul_speedyMetropolisGaussian {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) (x : EuclideanSpace ℝ (Fin n))
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T) :
    ell K δ x * gaussianWeight s x * speedyMetropolisGaussian K δ s x T
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
          (∫⁻ y in T ∩ K, gaussianWeight s x * metropolisDensity s δ x y)
        + T.indicator (fun z => ell K δ z * gaussianWeight s z *
            (1 - speedyMetropolisMove K δ s z)) x := by
  have hc : (∫⁻ y in T ∩ K, metropolisDensity s δ x y) ≤ volume (Metric.ball x δ ∩ K) :=
    (lintegral_metropolisDensity_le (T ∩ K) δ s x).trans
      (measure_mono (Set.inter_subset_inter_right _ Set.inter_subset_right))
  rw [speedyMetropolisGaussian_apply_set hK δ s x hT, mul_add]
  congr 1
  · calc ell K δ x * gaussianWeight s x *
          ((volume (Metric.ball x δ ∩ K))⁻¹ * ∫⁻ y in T ∩ K, metropolisDensity s δ x y)
        = gaussianWeight s x *
            (ell K δ x * ((volume (Metric.ball x δ ∩ K))⁻¹ *
              ∫⁻ y in T ∩ K, metropolisDensity s δ x y)) := by ring
      _ = gaussianWeight s x * ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
            ∫⁻ y in T ∩ K, metropolisDensity s δ x y) := by
          rw [ell_mul_inv_volume_inter_ball K δ x hc]
      _ = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
            (∫⁻ y in T ∩ K, gaussianWeight s x * metropolisDensity s δ x y) := by
          rw [lintegral_const_mul' _ _ (gaussianWeight_ne_top s x)]; ring
  · by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, mul_zero]

/-! ## 4. Reversibility -/

/-- **The flow of the speedy Metropolis–Gaussian walk against the `ℓ·γ`-weight, split into its
two parts.**  For `pi = ellGaussianMeasure K δ s`,

    flow(S, T) = vol(δBₙ)⁻¹ · ∫_{S ∩ K} ∫_{T ∩ K} g(x)·p(x,y) dy dx
                 + ∫_{T ∩ S ∩ K} ℓ(x)·g(x)·(1 − m(x)) dx.

Both terms are visibly symmetric under exchanging `S` and `T` — the first by
`lintegral_gaussianWeight_mul_metropolisDensity_comm`, the second because its domain of
integration is symmetric.  Note the `ℓ` has *vanished* from the first term: that is the whole
point of the speedy proposal. -/
theorem flow_speedyMetropolisGaussian {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) {S T : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    flow (speedyMetropolisGaussian K δ s) (ellGaussianMeasure K δ s) S T
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ *
            (∫⁻ x in S ∩ K, ∫⁻ y in T ∩ K, gaussianWeight s x * metropolisDensity s δ x y)
        + ∫⁻ x in T ∩ (S ∩ K), ell K δ x * gaussianWeight s x *
            (1 - speedyMetropolisMove K δ s x) := by
  have hker : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      speedyMetropolisGaussian K δ s x T := Kernel.measurable_coe _ hT
  rw [flow_apply, setLIntegral_ellGaussianMeasure hK δ s hS hker]
  simp_rw [ellGaussian_mul_speedyMetropolisGaussian hK δ s _ hT]
  rw [lintegral_add_left
      ((measurable_setLIntegral_gaussianWeight_mul_metropolisDensity s δ (T ∩ K)).const_mul _),
    lintegral_const_mul _
      (measurable_setLIntegral_gaussianWeight_mul_metropolisDensity s δ (T ∩ K)),
    lintegral_indicator hT, Measure.restrict_restrict hT]

/-- **The speedy Metropolis–Gaussian walk satisfies detailed balance for the unnormalised
`ℓ·γ`-weighted measure** `(volume.restrict K).withDensity (ℓ·g)`, `g(x) = e^{−‖x‖²/(2s)}`.

This is the deliverable: a kernel that is at once *speedy* (its normaliser cancels `ℓ`, so no
pointwise local-conductance floor is needed to make it move) and *Gaussian-targeted* (its
stationary law carries the Gaussian tilt that makes consecutive Cousins–Vempala phases
`O(1)`-warm).  No convexity of `K`, no positivity of `δ` or of `s`, and no bound relating `δ` to
`K` is required. -/
theorem isReversible_speedyMetropolisGaussian {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) :
    IsReversible (speedyMetropolisGaussian K δ s) (ellGaussianMeasure K δ s) := by
  intro S T hS hT
  have h2 : T ∩ (S ∩ K) = S ∩ (T ∩ K) := by
    ext y
    simp only [Set.mem_inter_iff]
    tauto
  rw [flow_speedyMetropolisGaussian hK δ s hS hT, flow_speedyMetropolisGaussian hK δ s hT hS,
    lintegral_gaussianWeight_mul_metropolisDensity_comm s δ (S ∩ K) (T ∩ K), h2]

/-! ## 5. Normalisation -/

/-- The **`ℓ·γ`-weighted probability measure** on `K`: the stationary distribution of the speedy
Metropolis–Gaussian walk.  A plain construction; `isProbabilityMeasure_ellGaussianProb` gives the
guards under which it is a probability measure, and
`isProbabilityMeasure_ellGaussianProb_unitBall` discharges them on the witness. -/
noncomputable def ellGaussianProb (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (ellGaussianMeasure K δ s Set.univ)⁻¹ • ellGaussianMeasure K δ s

/-- `ellGaussianProb` is a probability measure exactly when the total `ℓ·γ`-weight is positive and
finite; finiteness is automatic once `s > 0` and `vol(K) < ⊤` (`ellGaussianMeasure_univ_le`). -/
theorem isProbabilityMeasure_ellGaussianProb {K : Set (EuclideanSpace ℝ (Fin n))} {δ s : ℝ}
    (h0 : ellGaussianMeasure K δ s Set.univ ≠ 0) (htop : ellGaussianMeasure K δ s Set.univ ≠ ⊤) :
    IsProbabilityMeasure (ellGaussianProb K δ s) := by
  refine ⟨?_⟩
  rw [ellGaussianProb, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- **The walk is reversible for its stationary probability measure.** -/
theorem isReversible_speedyMetropolisGaussian_prob {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) :
    IsReversible (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) :=
  (isReversible_speedyMetropolisGaussian hK δ s).smul _

/-- **The `ℓ·γ`-weighted probability measure is invariant for the walk.** -/
theorem invariant_speedyMetropolisGaussian {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (δ s : ℝ) :
    Kernel.Invariant (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) :=
  (isReversible_speedyMetropolisGaussian_prob hK δ s).invariant

/-- **`ellGaussianProb` lives on `K`.** -/
theorem ellGaussianProb_compl_eq_zero {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ s : ℝ) : ellGaussianProb K δ s Kᶜ = 0 := by
  rw [ellGaussianProb, Measure.smul_apply, smul_eq_mul, ellGaussianMeasure_compl_eq_zero hK δ s,
    mul_zero]

/-- **`ellGaussianProb` is absolutely continuous for Lebesgue measure.** -/
theorem ellGaussianProb_absolutelyContinuous (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ) :
    ellGaussianProb K δ s ≪ volume := by
  intro t ht
  rw [ellGaussianProb, Measure.smul_apply, smul_eq_mul,
    ellGaussianMeasure_absolutelyContinuous K δ s ht, mul_zero]

/-! ## 6. Non-vacuity witness

Everything above is a true statement about the zero measure, or about a kernel that never moves,
unless the guards below are discharged.  They are, on the unit ball, for every dimension `n ≥ 1`,
every step `0 < δ ≤ 1/2` and every temperature `s > 0`. -/

/-- **The local conductance is `1` well inside the unit ball.**  For `‖x‖ < 1/2` and `δ ≤ 1/2` the
whole proposal ball lies inside `K`, so `ℓ(x) = 1`.  This is what stops the target measure
`ellGaussianMeasure` from being zero: `ℓ` is not everywhere small. -/
theorem ell_unitBall_eq_one {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) :
    ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x = 1 := by
  have hsub : Metric.ball x δ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro y hy
    have h1 : dist y x < δ := Metric.mem_ball.1 hy
    have h2 : dist x 0 < 1 / 2 := Metric.mem_ball.1 hx
    refine Metric.mem_ball.2 (lt_of_le_of_lt (dist_triangle y x 0) ?_)
    linarith
  rw [ell_apply, Set.inter_eq_self_of_subset_left hsub,
    ENNReal.div_self (Metric.measure_ball_pos volume x hδ).ne' measure_ball_lt_top.ne]

/-- The `ℓ·γ`-weighted measure of the unit ball is not zero — the first guard on the witness.
On `‖x‖ < 1/2` the weight is `ℓ(x)·g(x) = g(x) ≥ e^{−1/(8s)}`. -/
theorem ellGaussianMeasure_unitBall_ne_zero {δ s : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ellGaussianMeasure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ s Set.univ ≠ 0 := by
  rw [ellGaussianMeasure_univ]
  have hchain : ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * s))) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
      ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x * gaussianWeight s x := by
    calc ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) ^ 2 / (2 * s))) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
        ≤ ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2), gaussianWeight s y := by
          rw [← withDensity_apply _ measurableSet_ball]
          exact mul_volume_ball_le_withDensity_gaussianWeight hs (1 / 2)
      _ ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2),
            ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x * gaussianWeight s x :=
          setLIntegral_mono' measurableSet_ball fun x hx => by
            rw [ell_unitBall_eq_one hδ hδ2 hx, one_mul]
      _ ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
            ell (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ x * gaussianWeight s x :=
          lintegral_mono' (Measure.restrict_mono
            (Metric.ball_subset_ball (by norm_num)) le_rfl) le_rfl
  refine ne_of_gt (lt_of_lt_of_le ?_ hchain)
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos (-(1 / 2 : ℝ) ^ 2 / (2 * s)))).ne'
    (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n))
      (by norm_num : (0:ℝ) < 1 / 2)).ne'

/-- The `ℓ·γ`-weighted measure of the unit ball is finite — the second guard on the witness. -/
theorem ellGaussianMeasure_unitBall_ne_top {δ s : ℝ} (hs : 0 < s) :
    ellGaussianMeasure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ s Set.univ ≠ ⊤ :=
  ne_top_of_le_ne_top volume_unitBall_ne_top (ellGaussianMeasure_univ_le hs _ δ)

/-- **The target really is a probability measure on the witness.**  This is what stops
`isReversible_speedyMetropolisGaussian_prob` and `invariant_speedyMetropolisGaussian` from being
statements about the zero measure. -/
theorem isProbabilityMeasure_ellGaussianProb_unitBall {δ s : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    IsProbabilityMeasure
      (ellGaussianProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ s) :=
  isProbabilityMeasure_ellGaussianProb (ellGaussianMeasure_unitBall_ne_zero hs hδ hδ2)
    (ellGaussianMeasure_unitBall_ne_top hs)

/-- **The walk moves with probability exactly `m(x)`**: `P_x({x}ᶜ) = m(x)`.  As for
`metropolisGaussian`, `[NeZero n]` is not removable — in `EuclideanSpace ℝ (Fin 0)` the whole
space is one atom and `{x}ᶜ = ∅`. -/
theorem speedyMetropolisGaussian_apply_compl_singleton [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    speedyMetropolisGaussian K δ s x {x}ᶜ = speedyMetropolisMove K δ s x := by
  rw [speedyMetropolisGaussian_apply_set hK δ s x (measurableSet_singleton x).compl,
    Set.indicator_of_notMem (by simp), mul_zero, add_zero, ← ENNReal.div_eq_inv_mul,
    speedyMetropolisMove_apply]
  congr 1
  rw [show ({x}ᶜ ∩ K : Set (EuclideanSpace ℝ (Fin n))) = K \ {x} by
    rw [Set.sdiff_eq, Set.inter_comm]]
  exact setLIntegral_congr (sdiff_null_ae_eq_self (measure_singleton x))

/-- **The speedy proposal only helps the walk move.**  Same numerator, smaller denominator:
`vol(B(x,δ) ∩ K) ≤ vol(B(x,δ))`, so the speedy move probability dominates the plain Metropolis
one.  This is the quantitative form of "conditioning on landing in `K` never wastes a step", and
it transports `metropolisMove`'s positivity witness for free. -/
theorem metropolisMove_le_speedyMetropolisMove (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    metropolisMove K δ s x ≤ speedyMetropolisMove K δ s x := by
  rw [metropolisMove_apply, speedyMetropolisMove_apply]
  exact ENNReal.div_le_div_left (measure_mono Set.inter_subset_left) _

/-- **The witness kernel really moves**: from the centre of the unit ball with `0 < δ ≤ 1/2` and
`s > 0`, the probability of leaving the current point is at least `e^{−δ²/(2s)} > 0`. -/
theorem speedyMetropolisMove_unitBall_pos {δ s : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < speedyMetropolisMove (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ s 0 :=
  lt_of_lt_of_le (metropolisMove_unitBall_pos hs hδ hδ1)
    (metropolisMove_le_speedyMetropolisMove _ δ s 0)

/-- **From the origin the accepted mass over the unit ball is the Gaussian mass of the proposal
ball.**  For `δ ≤ 1` the proposal ball sits inside `K`, and `min(1, g(y)/g(0)) = g(y)`. -/
theorem lintegral_metropolisDensity_zero_unitBall {δ s : ℝ} (hs : 0 < s) (hδ1 : δ ≤ 1) :
    ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, metropolisDensity s δ 0 y
      = ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, gaussianWeight s y := by
  have hfun : metropolisAccept s (0 : EuclideanSpace ℝ (Fin n)) = gaussianWeight s :=
    funext (metropolisAccept_zero_left hs)
  simp_rw [metropolisDensity, hfun]
  rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
    Set.inter_eq_self_of_subset_left (Metric.ball_subset_ball hδ1)]

/-- **The filter genuinely rejects: the walk holds with positive probability.**
`m(0) < 1` on the witness, because `g < 1` off the origin and singletons are null.

This is the fact that distinguishes this kernel from `Arlib.MarkovChains.speedyWalk`, whose move
probability is exactly `1` at every non-stuck point: a speedy *Metropolis* step is rejected with
positive probability even though the proposal is always inside `K`.  Without it, "reversible for
`1_K·ℓ·γ`" could be a statement about a chain that never uses the Gaussian tilt. -/
theorem speedyMetropolisMove_unitBall_lt_one [NeZero n] {δ s : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    speedyMetropolisMove (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ s 0 < 1 := by
  have hV0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 hδ).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hle : ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, gaussianWeight s y
      ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
    calc ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, gaussianWeight s y
        ≤ ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, (1 : ℝ≥0∞) :=
          setLIntegral_mono' measurableSet_ball fun y _ => gaussianWeight_le_one hs y
      _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
          rw [setLIntegral_one]
  have hne : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hstrict : ∫⁻ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, gaussianWeight s y
      < ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, (1 : ℝ≥0∞) :=
    setLIntegral_strict_mono measurableSet_ball hV0 measurable_const
      (ne_top_of_le_ne_top hVtop hle)
      (hne.mono fun x hx _ => gaussianWeight_lt_one hs hx)
  rw [setLIntegral_one] at hstrict
  rw [speedyMetropolisMove_apply,
    Set.inter_eq_self_of_subset_left (Metric.ball_subset_ball hδ1),
    lintegral_metropolisDensity_zero_unitBall hs hδ1,
    ENNReal.div_lt_iff (Or.inl hV0) (Or.inl hVtop), one_mul]
  exact hstrict

/-- **The non-vacuity witness (`CLAUDE.md` §11), packaged.**  For every dimension `n ≥ 1`, every
step `0 < δ ≤ 1/2` and every temperature `s > 0` there is a body `K` — the unit ball — such that

* `K` is measurable, so every theorem above applies to it;
* `ellGaussianProb K δ s`, the normalised `1_K·ℓ·γ` law, is a genuine probability measure, not
  the zero measure;
* `speedyMetropolisGaussian K δ s` is a Markov kernel, reversible for the unnormalised measure
  *and* for the probability measure, and leaves the latter invariant;
* the walk leaves its current point with probability strictly between `0` and `1`: it really
  moves, and the Gaussian filter really rejects — so this is neither `dirac` nor
  `Arlib.MarkovChains.speedyWalk` in disguise;
* and the acceptance filter is non-trivial pointwise: from the centre every proposal `y ≠ 0` is
  accepted with probability `< 1`.

Without this every result above could be a true statement about a degenerate object. -/
theorem exists_speedyMetropolisGaussian_witness [NeZero n] {δ s : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hs : 0 < s) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet K ∧
        IsProbabilityMeasure (ellGaussianProb K δ s) ∧
        IsMarkovKernel (speedyMetropolisGaussian K δ s) ∧
        IsReversible (speedyMetropolisGaussian K δ s) (ellGaussianMeasure K δ s) ∧
        IsReversible (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) ∧
        Kernel.Invariant (speedyMetropolisGaussian K δ s) (ellGaussianProb K δ s) ∧
        speedyMetropolisGaussian K δ s 0 {(0 : EuclideanSpace ℝ (Fin n))}ᶜ
            = speedyMetropolisMove K δ s 0 ∧
        0 < speedyMetropolisGaussian K δ s 0 {(0 : EuclideanSpace ℝ (Fin n))}ᶜ ∧
        speedyMetropolisGaussian K δ s 0 {(0 : EuclideanSpace ℝ (Fin n))}ᶜ < 1 ∧
        ∀ y : EuclideanSpace ℝ (Fin n), y ≠ 0 → metropolisAccept s 0 y < 1 := by
  have hδ1 : δ ≤ 1 := by linarith
  have hcompl := speedyMetropolisGaussian_apply_compl_singleton
    (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1)) δ s 0
  refine ⟨Metric.ball 0 1, measurableSet_ball,
    isProbabilityMeasure_ellGaussianProb_unitBall hs hδ hδ2,
    isMarkovKernel_speedyMetropolisGaussian _ _ _,
    isReversible_speedyMetropolisGaussian measurableSet_ball δ s,
    isReversible_speedyMetropolisGaussian_prob measurableSet_ball δ s,
    invariant_speedyMetropolisGaussian measurableSet_ball δ s, hcompl, ?_, ?_,
    fun y hy => metropolisAccept_zero_lt_one hs hy⟩
  · rw [hcompl]
    exact speedyMetropolisMove_unitBall_pos hs hδ hδ1
  · rw [hcompl]
    exact speedyMetropolisMove_unitBall_lt_one hs hδ hδ1

/-! ## 7. What a conductance bound would still need — scope, not a theorem

**Nothing below is a declaration.**  This section exists so that no reader mistakes the kernel
above for a mixing result.

`Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex` (`StarPolar.lean:626`) is stated for
`Arlib.MarkovChains.speedyWalk` and **does not apply** to `speedyMetropolisGaussian`; the
conductance of this kernel does **not** follow from it, and nothing in this file implies it.

`Arlib.MarkovChains.conductance_speedyGaussian_ge` (`SpeedyConductanceSharp.lean:320`) is a
different matter: it is abstract in its kernel `P`, so it *would* accept this kernel.  Three
things are missing before it could be applied here, and none of them is proved anywhere in this
repository for this kernel:

1. **`hoverlap` for this kernel.**  The binder asks that a pair `u ∈ S ∩ K`, `v ∈ K \ S` with
   `‖u − v‖ < δ/√n` and `d_h(u,v) < 1/4` satisfy `1 ≤ 20·(P_u(Sᶜ) + P_v(S))`.  The repository's
   speedy overlap lemmas (`SpeedyOverlap.lean`, `OverlapSqrt.lean`,
   `Arlib.MarkovChains.one_le_speedyWalk_add_speedyWalk_compl`) are about `speedyWalk`, whose
   one-step law is *uniform* on `B(x,δ) ∩ K`.  Here the acceptance filter thins that law by
   `min(1, g(y)/g(x))`, so the geometric overlap estimate must be multiplied by an acceptance
   floor over the overlap region — the estimate `e^{−(2Rδ+δ²)/(2s)}` that
   `MetropolisConductanceSharp.lean` derives for `metropolisGaussian`, re-derived against the
   speedy normaliser.  That is a genuine proof obligation, not bookkeeping.
2. **The `hpi` bridge.**  `conductance_speedyGaussian_ge` takes its stationary law in the *real*
   density form `pi A = ofReal (∫_A h) / ofReal (∫ h)`.  `ellGaussianProb` is built from an
   `ℝ≥0∞` density `ℓ·g`; identifying the two requires `h = (ell K δ ·).toReal · gaussianWeightReal`
   together with the integrability facts that make `ofReal` commute with the integral.
3. **`hiso` wiring.**  `Arlib.ellGaussian_isoperimetry_measurable_logTwo`
   (`Arlib/Convexity/IsoWeighted.lean`) is the isoperimetric input for exactly this density, but
   it carries `hellKpos`, `hellLip` and `hLσ` — strict positivity of `ℓ` on `K`, log-Lipschitzness
   of `ℓ` on `K` with an explicit constant `Lf`, and the compatibility `√3·(σ²Lf + R) ≤ 2σ√n`.
   Those three must be discharged for the body and parameters at hand before its conclusion can be
   fed to `conductance_speedyGaussian_ge`'s `hiso` binder.

So: this file closes the *kernel* gap.  It does not close the conductance gap, the mixing gap, or
any runtime gap, and it must not be quoted as doing so. -/

end Arlib.MarkovChains

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Arlib.MarkovChains.speedyMetropolisMove_apply
#print axioms Arlib.MarkovChains.lintegral_metropolisDensity_le
#print axioms Arlib.MarkovChains.speedyMetropolisMove_le_one
#print axioms Arlib.MarkovChains.measurable_speedyMetropolisMove
#print axioms Arlib.MarkovChains.speedyMetropolisGaussianAux_apply
#print axioms Arlib.MarkovChains.speedyMetropolisGaussian_eq
#print axioms Arlib.MarkovChains.speedyMetropolisGaussian_apply_set
#print axioms Arlib.MarkovChains.isMarkovKernel_speedyMetropolisGaussianAux
#print axioms Arlib.MarkovChains.isMarkovKernel_speedyMetropolisGaussian
#print axioms Arlib.MarkovChains.measurable_ell_mul_gaussianWeight
#print axioms Arlib.MarkovChains.ellGaussianMeasure_univ
#print axioms Arlib.MarkovChains.ellGaussianMeasure_compl_eq_zero
#print axioms Arlib.MarkovChains.ellGaussianMeasure_absolutelyContinuous
#print axioms Arlib.MarkovChains.ellGaussianMeasure_univ_le
#print axioms Arlib.MarkovChains.setLIntegral_ellGaussianMeasure
#print axioms Arlib.MarkovChains.ell_mul_inv_volume_inter_ball
#print axioms Arlib.MarkovChains.ellGaussian_mul_speedyMetropolisGaussian
#print axioms Arlib.MarkovChains.flow_speedyMetropolisGaussian
#print axioms Arlib.MarkovChains.isReversible_speedyMetropolisGaussian
#print axioms Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb
#print axioms Arlib.MarkovChains.isReversible_speedyMetropolisGaussian_prob
#print axioms Arlib.MarkovChains.invariant_speedyMetropolisGaussian
#print axioms Arlib.MarkovChains.ellGaussianProb_compl_eq_zero
#print axioms Arlib.MarkovChains.ellGaussianProb_absolutelyContinuous
#print axioms Arlib.MarkovChains.ell_unitBall_eq_one
#print axioms Arlib.MarkovChains.ellGaussianMeasure_unitBall_ne_zero
#print axioms Arlib.MarkovChains.ellGaussianMeasure_unitBall_ne_top
#print axioms Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb_unitBall
#print axioms Arlib.MarkovChains.speedyMetropolisGaussian_apply_compl_singleton
#print axioms Arlib.MarkovChains.metropolisMove_le_speedyMetropolisMove
#print axioms Arlib.MarkovChains.speedyMetropolisMove_unitBall_pos
#print axioms Arlib.MarkovChains.lintegral_metropolisDensity_zero_unitBall
#print axioms Arlib.MarkovChains.speedyMetropolisMove_unitBall_lt_one
#print axioms Arlib.MarkovChains.exists_speedyMetropolisGaussian_witness
