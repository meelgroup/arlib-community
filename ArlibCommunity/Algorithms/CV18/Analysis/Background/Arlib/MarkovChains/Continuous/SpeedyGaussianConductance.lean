/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyGaussian
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.OverlapSqrt
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisConductanceSharp
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.IsoWeighted

/-!
# A conductance bound for the speedy Metropolis–Gaussian walk

`Arlib/MarkovChains/Continuous/SpeedyGaussian.lean` builds
`Arlib.MarkovChains.speedyMetropolisGaussian` — the speedy proposal (uniform on `B(x,δ) ∩ K`)
with the Gaussian Metropolis filter `min(1, g(y)/g(x))` — and proves it reversible for
`1_K·ℓ·e^{−‖x‖²/(2s)}`.  Its §7 states, in prose and without declarations, the three things that
stand between that kernel and a conductance bound.  **This file discharges all three**, against
the abstract theorem `Arlib.MarkovChains.conductance_speedyGaussian_ge`
(`SpeedyConductanceSharp.lean:320`), and composes them.

## Main results, in the order of `SpeedyGaussian.lean` §7

* **Obligation 2, `Arlib.MarkovChains.hpi_ellGaussian`.**  `conductance_speedyGaussian_ge` takes
  its stationary law in the *real*-density form `π A = ofReal(∫_A h)/ofReal(∫ h)`;
  `ellGaussianProb` is built from an `ℝ≥0∞` density.  They agree at
  `h = 1_K·(ℓ.toReal)·gaussianWeightReal s`, both factors being bounded by `1` and hence
  Bochner-integrable on a `K` of finite volume.  The template is
  `Arlib.MarkovChains.uniformOn_gaussianWeight_eq_div` (`MetropolisConductanceSharp.lean:353`),
  which does the same job for the unweighted `1_K·γ`.
* **Obligation 3, `Arlib.MarkovChains.hiso_speedyMetropolisGaussian`.**  A single `exact` into
  `Arlib.ellGaussian_isoperimetry_measurable_logTwo` (`Arlib/Convexity/IsoWeighted.lean:851`) at
  `d := δ·ln 2/√n`.  Of its three external hypotheses only `hellKpos` is discharged
  (`ell_toReal_pos_of_convex`); `hellLip` and `hLσ` are **carried**, see below.
* **Obligation 1, `Arlib.MarkovChains.hoverlap_speedyMetropolisGaussian`.**  The substantive
  work.  The repository's speedy overlap estimates
  (`Arlib.MarkovChains.one_le_twelve_mul_speedyWalk_add_of_comparable`, `OverlapSqrt.lean:439`)
  are about the *uniform* law on `B(x,δ) ∩ K`; the filter thins that law by `min(1, g(y)/g(x))`,
  so every domination step loses an acceptance factor.
  `Arlib.MarkovChains.mul_volume_le_speedyMetropolisGaussian` re-runs the domination against the
  **speedy** normaliser `vol(B(x,δ) ∩ K)` in place of the Metropolis normaliser `vol(δBₙ)` of
  `Arlib.MarkovChains.mul_volume_le_metropolisGaussian`, bounding it by a common `M` so the two
  endpoints of an overlap pair combine.  The acceptance floor itself
  (`Arlib.MarkovChains.metropolisAccept_ge`) is kernel-independent and is reused verbatim.
* **The composition, `Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge`.**

## The constants are re-derived, not copied

The final bound `Φ ≥ δ·ln 2/(640·σ·√n)` is `conductance_speedyGaussian_ge`'s, whose module
docstring already records two corrections to the paper's `δ/(250σ√n)`.  The constants this file
adds are these:

* `20·(1/8)·(2/3) = 5/3`, from the sharpened Lemma 3.5 at separation `δ/√n`
  (`Arlib.MarkovChains.volume_lens_ge_min_ball_inter_sharp`, constant `1/8`) and the
  comparability `max ≤ (3/2)·min`.  So the overlap needs an acceptance floor `a ≥ 3/5` — the
  filtered analogue of the unfiltered walk's `1 ≤ 12·(…)`.
* `a ≥ 3/5` whenever `2Rδ + δ² ≤ (4/5)·s` (`acceptance_floor_of_le`), proved from
  `Real.add_one_le_exp` alone: `e^{−t} ≥ 1 − t ≥ 3/5` for `t ≤ 2/5`.  No logarithm, no numerical
  evaluation of `exp`.
* In the Cousins–Vempala regime `s = σ²`, `δ ≤ σ/(8√n)`, `R ≤ 2σ√n`
  (`acceptance_floor_of_cv`): `2Rδ ≤ σ²/2` and `δ² ≤ σ²/64`, so `2Rδ + δ² ≤ (33/64)σ²`, well
  inside `(4/5)σ²`.  `3/5` is weaker than the `e^{−1/8} ≈ 0.88` the exponential actually gives,
  and deliberately so: `3/5` is all the conclusion needs.

## Scope: what remains a hypothesis

`conductance_speedyMetropolisGaussian_ge` is **conditional**, and this file contains no mixing
bound, no spectral-gap bound and no runtime statement in any form.  Two hypotheses carry real
content and neither is proved here or anywhere in this repository:

* `hcomp`, Cousins–Vempala's `d_ℓ(u,v) < 1/3` (`1409.6011/vol3_journal.tex:581`) as a *global*
  premise on `K` — `hoverlap`'s binder admits no per-pair premise.  This is the same premise
  `Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable_global` carries for the
  unfiltered walk, and `Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample`
  shows it genuinely restricts `K`.
* `hellLip` and `hLσ`, from `Arlib.ellGaussian_isoperimetry_measurable_logTwo`.  Nothing here
  discharges log-Lipschitzness of `ℓ` for a general convex body;
  `Arlib.ellGaussian_isoperimetry_measurable_logTwo_strict_witness` obtains it only at `Lf = 0`,
  on a body small enough that `ℓ` is constant.

Everything else `conductance_speedyGaussian_ge` asks for **is** discharged here: `hh0`, `hmass`
(`integral_ellGaussianIndicator_pos`), `hpi`, `hrev`, `hpiK`, `hoverlap`, and `hiso`'s
`hellKpos`.  The acceptance floor is discharged from `hδσ` and `hRσ` alone.

## What was reused rather than rebuilt

`Arlib.MarkovChains.metropolisAccept_ge` and
`Arlib.MarkovChains.mul_volume_le_setLIntegral_metropolisDensity`
(`MetropolisConductanceSharp.lean`) are statements about `metropolisDensity`, not about any
kernel, and `Arlib.MarkovChains.speedyMetropolisGaussian_apply_set` produces exactly the
`∫⁻ y in A ∩ K, metropolisDensity s δ x y` they bound — so the acceptance floor needed no
re-derivation, only a new normaliser.  Likewise
`Arlib.MarkovChains.volume_lens_ge_min_ball_inter_sharp` and
`Arlib.MarkovChains.max_volume_ball_inter_le_of_ell_comparable` (`OverlapSqrt.lean`) are pure
geometry and are used unchanged.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The `π ↔ h` bridge -/

/-- The real form of the `ℓ·γ` density, `1_K(x)·ℓ(x)·e^{−‖x‖²/(2s)}`. -/
theorem ell_mul_gaussianWeight_eq_ofReal (K : Set (EuclideanSpace ℝ (Fin n))) (δ s : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ell K δ x * gaussianWeight s x
      = ENNReal.ofReal ((ell K δ x).toReal * gaussianWeightReal s x) := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ x))]
  rfl

/-- The `ℓ·γ` density is integrable on every set of finite volume: it is measurable and
bounded by `1`, both factors being at most `1`. -/
theorem integrableOn_ell_mul_gaussianWeightReal {s : ℝ} (hs : 0 < s)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (δ : ℝ)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hAtop : volume A ≠ ⊤) :
    IntegrableOn (fun x => (ell K δ x).toReal * gaussianWeightReal s x) A volume := by
  refine Measure.integrableOn_of_bounded (M := 1) hAtop
    (((measurable_ell hK δ).ennreal_toReal.mul
      (continuous_gaussianWeightReal s).measurable).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hell1 : (ell K δ x).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K δ x)
    simpa using this
  have hell0 : (0 : ℝ) ≤ (ell K δ x).toReal := ENNReal.toReal_nonneg
  have hg1 : gaussianWeightReal s x ≤ 1 := gaussianWeightReal_le_one hs x
  have hg0 : (0 : ℝ) < gaussianWeightReal s x := gaussianWeightReal_pos s x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

/-- **The measure form equals the density form.**  For
`h = 1_K · ℓ · e^{−‖x‖²/(2s)}`,

    ellGaussianMeasure K δ s A = ofReal (∫_A h). -/
theorem ellGaussianMeasure_eq_ofReal_setIntegral {s : ℝ} (hs : 0 < s)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤) (δ : ℝ)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    ellGaussianMeasure K δ s A
      = ENNReal.ofReal (∫ x in A,
          Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal s y) x) := by
  have hAKtop : volume (A ∩ K) ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (measure_mono Set.inter_subset_right)
  rw [ellGaussianMeasure, withDensity_apply _ hA, Measure.restrict_restrict hA,
    setIntegral_indicator hK,
    ofReal_integral_eq_lintegral_ofReal
      (integrableOn_ell_mul_gaussianWeightReal hs hK δ hAKtop)
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg ENNReal.toReal_nonneg (gaussianWeightReal_pos s x).le)]
  exact setLIntegral_congr_fun (hA.inter hK)
    (fun x _ => ell_mul_gaussianWeight_eq_ofReal K δ s x)

/-- **`hpi` for the speedy Metropolis–Gaussian chain** — obligation 2 of `SpeedyGaussian.lean`
§7, in exactly the form `Arlib.MarkovChains.conductance_speedyGaussian_ge` consumes:

    ellGaussianProb K δ s A  =  ofReal (∫_A h) / ofReal (∫ h),
    h = 1_K · ℓ · e^{−‖x‖²/(2s)}.

`ellGaussianProb` is the normalisation of an `ℝ≥0∞`-density measure; the consumer wants a
*real*-density quotient.  The two agree because both factors of the density are bounded by `1`
(`ell_le_one`, `gaussianWeight_le_one`) and hence Bochner-integrable on the finite-volume `K`. -/
theorem hpi_ellGaussian {s : ℝ} (hs : 0 < s) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤) (δ : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A) :
    ellGaussianProb K δ s A
      = ENNReal.ofReal (∫ x in A,
            Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal s y) x)
        / ENNReal.ofReal (∫ x,
            Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal s y) x) := by
  have huniv := ellGaussianMeasure_eq_ofReal_setIntegral hs hK hKtop δ
    (MeasurableSet.univ (α := EuclideanSpace ℝ (Fin n)))
  rw [setIntegral_univ] at huniv
  rw [ellGaussianProb, Measure.smul_apply, smul_eq_mul, huniv,
    ellGaussianMeasure_eq_ofReal_setIntegral hs hK hKtop δ hA, ← ENNReal.div_eq_inv_mul]

/-! ## 2. The isoperimetric input -/

/-- **`hellKpos` is free on a bounded convex body of positive volume.**  `ℓ(x) ≠ ⊤` because
`ℓ ≤ 1` (`Arlib.MarkovChains.ell_le_one`), and `ℓ(x) ≠ 0` because `vol(B(x,δ) ∩ K) ≠ 0`
(`Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex`, which needs no floor on `ℓ` at all —
contracting `K` towards `x` produces positive volume inside every ball). -/
theorem ell_toReal_pos_of_convex {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ x ∈ K, 0 < (ell K δ x).toReal := by
  intro x hx
  refine ENNReal.toReal_pos
    (ell_ne_zero_of_volume_ball_inter_ne_zero hδ
      (volume_ball_inter_ne_zero_of_convex hKc hKb hK0 hx hδ))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ x))

/-- **`hiso` for the speedy Metropolis–Gaussian chain** — obligation 3 of `SpeedyGaussian.lean`
§7, in exactly the binder shape of `Arlib.MarkovChains.conductance_speedyGaussian_ge`'s `hiso`,
at `s = σ²`.

The mathematics is entirely `Arlib.ellGaussian_isoperimetry_measurable_logTwo`
(`Arlib/Convexity/IsoWeighted.lean`), instantiated at `d := δ·ln 2/√n`; the body of the proof is
a single `exact`, so any drift between the two statements is a type error rather than a silent
mismatch.  Of that theorem's three external hypotheses, only `hellKpos` is discharged here
(`ell_toReal_pos_of_convex`, from bounded convexity and positive volume).

**`hellLip` and `hLσ` are carried, not proved.**  `hellLip` asks that `x ↦ ℓ(x)` be
log-Lipschitz on `K` with an explicit constant `Lf`, and `hLσ` that
`√3·(σ²Lf + R) ≤ 2σ√n`.  Nothing in this repository discharges `hellLip` for a general convex
body; `Arlib.ellGaussian_isoperimetry_measurable_logTwo_strict_witness` gets it only at `Lf = 0`,
on a body small enough that `ℓ` is constant.  So every downstream statement of this file is
**conditional on `hellLip` and `hLσ`** and may not be quoted otherwise.

**And there is reason to believe no witness with non-constant `ℓ` exists at the operative
step.**  The following argument is *informal* — it is not machine-checked, and is recorded so
that no one spends effort trying to discharge `hellLip` before reading it.  `hLσ` caps
`Lf ≤ 2√n/(√3·σ)`, so across a distance `δ ≤ σ/(8√n)` the permitted variation of `log ℓ` is
`Lf·δ ≤ 2/(8√3) ≈ 0.144`.  But `ℓ ≤ 2⁻ⁿ` at a cube corner
(`Arlib.MarkovChains.two_pow_mul_ell_cube_corner_le_one`, which *is* machine-checked) and
`≈ 1` at distance `δ√n` inward, a rate of `≈ √n·log 2/δ = 8n·log 2/σ`, exceeding the cap for
every `n ≥ 1`.

`hellLip` is an artefact of this repository's route, not of the mathematics: Cousins–Vempala's
`thm:iso` (`1409.6011/vol3_journal.tex:467`) uses no Lipschitz control of `ℓ` anywhere.  It
enters at exactly one place, `Arlib.norm_sub_ge_of_densDist_weighted`
(`Arlib/Convexity/IsoWeighted.lean:237`), which turns the density branch into a *metric*
separation so that disjoint open enlargements can lift the isoperimetric inequality from
open/closed sets to measurable ones.  The `ℓ`-weighted inequality itself is already proved
with no Lipschitz hypothesis, for `S₁, S₂` open and `S₃` closed:
`Arlib.ellGaussian_isoperimetry_openClosed_logTwo` (`Arlib/Convexity/EllLogConcave.lean:474`).
**UPDATE (same day): that upgrade is done, and this theorem is superseded.**
`Arlib.hiso_speedyMetropolisGaussian_uncond` (`Arlib/Convexity/SpeedyGaussianUncond.lean`)
is this binder with `hellLip`, `hLσ`, `hKR` and the parameters `R`, `Lf` all removed, and
`Arlib.conductance_speedyMetropolisGaussian_ge_uncond` is the conductance bound built on it,
with an unconditional witness.  Prefer those.  The theorems in *this* file remain correct but
carry hypotheses with no known witness at non-constant `ℓ`; see `AUDIT.md` §0i and §0k. -/
theorem hiso_speedyMetropolisGaussian (hn : 2 ≤ n) {σ δ R Lf : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hLf : 0 ≤ Lf) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hK0 : volume K ≠ 0)
    (hellLip : ∀ u ∈ K, ∀ v ∈ K,
      (ell K δ u).toReal ≤ (ell K δ v).toReal * Real.exp (Lf * ‖u - v‖))
    (hLσ : Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n) :
    ∀ S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n)),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K
                (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y)) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K
                (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
            * ∫ x in S₂, Set.indicator K
                (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
        ≤ (∫ x, Set.indicator K
              (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in S₃, Set.indicator K
              (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x := by
  intro S₁ S₂ S₃ hpart hS₁ hS₂ hS₃ hsep
  exact Arlib.ellGaussian_isoperimetry_measurable_logTwo (d := δ * Real.log 2 / Real.sqrt n)
    hn hσ hδ.le hLf hK hKc hKR hK0
    (ell_toReal_pos_of_convex hKc hKb hK0 hδ) hellLip hLσ hpart hS₁ hS₂ hS₃ hsep

/-! ## 3. The overlap estimate -/

/-- **Domination of the speedy Metropolis–Gaussian one-step law.**  For `‖x‖ ≤ R`, any region
`C` inside the proposal ball `B(x,δ)`, and any `M ≥ vol(B(x,δ) ∩ K)`,

    a · M⁻¹ · vol(A ∩ C ∩ K)  ≤  P_x(A),    a = e^{−(2Rδ+δ²)/(2s)}.

This is the speedy analogue of `Arlib.MarkovChains.mul_volume_le_metropolisGaussian`, and the
difference is exactly the one `SpeedyGaussian.lean` §7 names: there the normaliser is the
*constant* `vol(δBₙ)`, here it is the *centre-dependent* `vol(B(x,δ) ∩ K)`.  Bounding the latter
by a common `M` is what lets the two endpoints of an overlap pair be combined, and it is why the
estimate needs no floor on `ℓ` — only comparability of the two slice volumes downstream.

The acceptance floor itself is unchanged: `Arlib.MarkovChains.metropolisAccept_ge` is a statement
about `metropolisDensity`, not about any kernel, and
`Arlib.MarkovChains.mul_volume_le_setLIntegral_metropolisDensity` bounds precisely the
`∫⁻ y in A ∩ K, metropolisDensity s δ x y` that `speedyMetropolisGaussian_apply_set` produces.
The rejection atom is discarded; it can only help. -/
theorem mul_volume_le_speedyMetropolisGaussian {s : ℝ} (hs : 0 < s) {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 < δ) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ R) {M : ℝ≥0∞}
    (hM : volume (Metric.ball x δ ∩ K) ≤ M)
    {C A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hCK : MeasurableSet (C ∩ K)) (hC : C ⊆ Metric.ball x δ) :
    ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) * M⁻¹ * volume (A ∩ (C ∩ K))
      ≤ speedyMetropolisGaussian K δ s x A := by
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) with hadef
  have hkey : a * volume (A ∩ (C ∩ K)) ≤ ∫⁻ y in A ∩ K, metropolisDensity s δ x y :=
    mul_volume_le_setLIntegral_metropolisDensity hs hR hδ hx hA hCK hC
  rw [speedyMetropolisGaussian_apply_set hK δ s x hA]
  refine le_trans ?_ le_self_add
  calc a * M⁻¹ * volume (A ∩ (C ∩ K)) = M⁻¹ * (a * volume (A ∩ (C ∩ K))) := by ring
    _ ≤ (volume (Metric.ball x δ ∩ K))⁻¹ * (∫⁻ y in A ∩ K, metropolisDensity s δ x y) :=
        mul_le_mul' (ENNReal.inv_le_inv.2 hM) hkey

/-- **`cor:overlap` for `speedyMetropolisGaussian`, at separation `δ/√n`** — obligation 1 of
`SpeedyGaussian.lean` §7, in its core per-pair form.

The skeleton is `Arlib.MarkovChains.one_le_twelve_mul_speedyWalk_add_of_comparable`:

* both one-step laws dominate the uniform law on the lens `C = B(u,δ) ∩ B(v,δ)`, each normalised
  by the larger `M` of the two slice volumes;
* `T` and `Tᶜ` partition, so the two numerators add up to `vol(C ∩ K)`;
* `vol(C ∩ K) ≥ (1/8)·min` by `Arlib.MarkovChains.volume_lens_ge_min_ball_inter_sharp`, and
  `min ≥ (2/3)·M` by comparability.

**What is new is the factor `a = e^{−(2Rδ+δ²)/(2s)}.**  The Metropolis filter thins the uniform
proposal by `min(1, g(y)/g(x))`, so every domination step above loses that factor, and the
speedy walk's `1 ≤ 12·(…)` becomes `1 ≤ 20·(…)` only once `a` is bounded below.  That is the
content of `hfloor`, which is `1 ≤ 20·a·(1/8)·(2/3)`, i.e. `a ≥ 3/5`; see
`three_fifths_le_acceptance_floor` for its discharge.  The floor is *not* copied from
Cousins–Vempala: `20·(1/8)·(2/3) = 5/3` is computed from the two constants above.

No lower bound on `ℓ` is used — only `hu0`, that the accepted part of `u`'s proposal ball is
non-null, which `Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex` gives for free on a
bounded convex body of positive volume. -/
theorem one_le_twenty_mul_speedyMetropolisGaussian_add_of_comparable (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    {δ s R : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hR : 0 ≤ R)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K)
    (hRu : ‖u‖ ≤ R) (hRv : ‖v‖ ≤ R)
    (hsep : ‖u - v‖ ≤ δ / Real.sqrt n) (hu0 : volume (Metric.ball u δ ∩ K) ≠ 0)
    (hcomp : max (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K))
      ≤ ENNReal.ofReal (3 / 2)
          * min (volume (Metric.ball u δ ∩ K)) (volume (Metric.ball v δ ∩ K)))
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 / 8) * (2 / 3))
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : MeasurableSet T) :
    1 ≤ 20 * (speedyMetropolisGaussian K δ s u Tᶜ + speedyMetropolisGaussian K δ s v T) := by
  set C : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball u δ ∩ Metric.ball v δ with hCdef
  have hCK : MeasurableSet (C ∩ K) := (measurableSet_ball.inter measurableSet_ball).inter hK
  set p : ℝ≥0∞ := volume (Metric.ball u δ ∩ K) with hpdef
  set q : ℝ≥0∞ := volume (Metric.ball v δ ∩ K) with hqdef
  set M : ℝ≥0∞ := max p q with hMdef
  set m : ℝ≥0∞ := min p q with hmdef
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s))) with hadef
  have hM0 : M ≠ 0 := by
    intro hc
    refine hu0 ?_
    have hle : p ≤ 0 := hc ▸ le_max_left p q
    simpa using hle
  have hMtop : M ≠ ⊤ := by
    rw [hMdef, hpdef, hqdef]
    refine ne_of_lt (max_lt ?_ ?_) <;>
      exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top
  -- both one-step laws dominate the thinned uniform law on the lens, normalised by `M`
  have h1 : a * M⁻¹ * volume (Tᶜ ∩ (C ∩ K)) ≤ speedyMetropolisGaussian K δ s u Tᶜ :=
    mul_volume_le_speedyMetropolisGaussian hs hR hδ hK hRu (le_max_left _ _) hT.compl hCK
      Set.inter_subset_left
  have h2 : a * M⁻¹ * volume (T ∩ (C ∩ K)) ≤ speedyMetropolisGaussian K δ s v T :=
    mul_volume_le_speedyMetropolisGaussian hs hR hδ hK hRv (le_max_right _ _) hT hCK
      Set.inter_subset_right
  -- `T` and `Tᶜ` partition the lens: the two numerators add up
  have h3 : volume (Tᶜ ∩ (C ∩ K)) + volume (T ∩ (C ∩ K)) = volume (C ∩ K) := by
    have hmeas := measure_inter_add_sdiff (μ := volume) (C ∩ K) hT
    rw [Set.inter_comm (C ∩ K) T, Set.sdiff_eq, Set.inter_comm (C ∩ K) Tᶜ] at hmeas
    rw [add_comm]
    exact hmeas
  -- Lemma 3.5 at `δ/√n`, sharpened
  have hlens : ENNReal.ofReal (1 / 8) * m ≤ volume (C ∩ K) :=
    volume_lens_ge_min_ball_inter_sharp hn hKc hu hv hδ hsep
  -- comparability, in the multiplied-out form `(2/3)·M ≤ m`
  have hMm : ENNReal.ofReal (2 / 3) * M ≤ m := by
    have hprod : ENNReal.ofReal (2 / 3) * ENNReal.ofReal (3 / 2) = 1 := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2 / 3)]
      norm_num
    calc ENNReal.ofReal (2 / 3) * M
        ≤ ENNReal.ofReal (2 / 3) * (ENNReal.ofReal (3 / 2) * m) := by gcongr
      _ = (ENNReal.ofReal (2 / 3) * ENNReal.ofReal (3 / 2)) * m := by ring
      _ = m := by rw [hprod, one_mul]
  have hconst : ENNReal.ofReal
      (20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 / 8) * (2 / 3))
      = 20 * (a * ENNReal.ofReal (1 / 8) * ENNReal.ofReal (2 / 3)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 20), hadef,
      show ENNReal.ofReal (20 : ℝ) = (20 : ℝ≥0∞) by simp]
    ring
  calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    _ ≤ ENNReal.ofReal
          (20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 / 8) * (2 / 3)) :=
        ENNReal.ofReal_le_ofReal hfloor
    _ = 20 * (a * ENNReal.ofReal (1 / 8) * ENNReal.ofReal (2 / 3)) := hconst
    _ = 20 * (a * M⁻¹ * (ENNReal.ofReal (1 / 8) * (ENNReal.ofReal (2 / 3) * M))) := by
        rw [show a * M⁻¹ * (ENNReal.ofReal (1 / 8) * (ENNReal.ofReal (2 / 3) * M))
            = a * ENNReal.ofReal (1 / 8) * ENNReal.ofReal (2 / 3) * (M⁻¹ * M) by ring,
          ENNReal.inv_mul_cancel hM0 hMtop, mul_one]
    _ ≤ 20 * (a * M⁻¹ * (ENNReal.ofReal (1 / 8) * m)) := by gcongr
    _ ≤ 20 * (a * M⁻¹ * volume (C ∩ K)) := by gcongr
    _ = 20 * (a * M⁻¹ * volume (Tᶜ ∩ (C ∩ K)) + a * M⁻¹ * volume (T ∩ (C ∩ K))) := by
        rw [← mul_add, h3]
    _ ≤ 20 * (speedyMetropolisGaussian K δ s u Tᶜ + speedyMetropolisGaussian K δ s v T) := by
        gcongr

/-- **The acceptance floor, re-derived.**  `1 ≤ 20·a·(1/8)·(2/3)` — that is, `a ≥ 3/5` — as soon
as `2Rδ + δ² ≤ (4/5)·s`.

No logarithm and no numerical evaluation of `exp`: `Real.add_one_le_exp` gives
`e^{−t} ≥ 1 − t ≥ 3/5` for `t ≤ 2/5`, and `20·(1/8)·(2/3) = 5/3` turns that into `≥ 1`
*exactly*.  The constant `4/5` is therefore the largest this argument allows and is computed,
not quoted. -/
theorem acceptance_floor_of_le {R δ s : ℝ} (hs : 0 < s)
    (hsmall : 2 * R * δ + δ ^ 2 ≤ 4 / 5 * s) :
    1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 / 8) * (2 / 3) := by
  have h2s : (0 : ℝ) < 2 * s := by linarith
  have ht : (2 * R * δ + δ ^ 2) / (2 * s) ≤ 2 / 5 := by
    rw [div_le_iff₀ h2s]; linarith
  have hneg : -(2 * R * δ + δ ^ 2) / (2 * s) = -((2 * R * δ + δ ^ 2) / (2 * s)) := by ring
  have hexp : 1 - (2 * R * δ + δ ^ 2) / (2 * s)
      ≤ Real.exp (-((2 * R * δ + δ ^ 2) / (2 * s))) := by
    have := Real.add_one_le_exp (-((2 * R * δ + δ ^ 2) / (2 * s)))
    linarith
  rw [hneg]
  linarith

/-- **The acceptance floor in the Cousins–Vempala regime.**  At `s = σ²`, with the step size
`δ ≤ σ/(8√n)` that `Arlib.MarkovChains.conductance_speedyGaussian_ge` already assumes and a body
inside `‖x‖ ≤ 2σ√n`,

    2Rδ + δ²  ≤  σ²/2 + σ²/64  =  (33/64)·σ²  ≤  (4/5)·σ²,

so `acceptance_floor_of_le` applies.  Both estimates are re-derived here: `2Rδ ≤ 2·(2σ√n)·δ` and
`8√n·δ ≤ σ` give `2Rδ ≤ σ²/2`, while `√n ≥ 1` gives `δ ≤ σ/8` and hence `δ² ≤ σ²/64`.  The
resulting `a ≥ 3/5` is weaker than the `e^{−1/8} ≈ 0.88` one gets by evaluating the exponential,
and deliberately so — `3/5` is all the conclusion needs and it costs no transcendental
arithmetic. -/
theorem acceptance_floor_of_cv (hn : 2 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hRσ : R ≤ 2 * σ * Real.sqrt n) :
    1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 8) * (2 / 3) := by
  have ht1 : (1 : ℝ) ≤ Real.sqrt n := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hn1
  have htpos : (0 : ℝ) < Real.sqrt n := lt_of_lt_of_le one_pos ht1
  have h8t : δ * (8 * Real.sqrt n) ≤ σ := (le_div_iff₀ (by positivity)).1 hδσ
  have hδ8 : 8 * δ ≤ σ := by nlinarith
  have hRδ : 2 * R * δ ≤ σ ^ 2 / 2 := by nlinarith
  have hδ2 : δ ^ 2 ≤ σ ^ 2 / 64 := by nlinarith
  refine acceptance_floor_of_le (by positivity) ?_
  nlinarith

/-- **`hoverlap` for the speedy Metropolis–Gaussian chain** — obligation 1 of
`SpeedyGaussian.lean` §7, in exactly the binder shape of
`Arlib.MarkovChains.conductance_speedyGaussian_ge`'s `hoverlap`.

Comparability of the local conductances is a **global** hypothesis on `K`, as it must be:
`hoverlap`'s binder admits no extra per-pair premise, and this is the same shape
`Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable_global` uses for the unfiltered
speedy walk.  It is Cousins–Vempala's `d_ℓ(u,v) < 1/3` (`vol3_journal.tex:581`) written
division-free; `Arlib.MarkovChains.ell_le_of_densDist_ell_lt` proves the two are the same
hypothesis.  It is stated one-sidedly and applied in both directions via `norm_sub_rev`.

`u ∈ T`, `v ∉ T` and `densDist h u v < 1/4` are not used; they are carried only so that the
statement lines up with the consumer, clause for clause.

**This is not a conductance bound and not a mixing bound**; it is one hypothesis of one. -/
theorem hoverlap_speedyMetropolisGaussian (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {δ s R : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ < δ / Real.sqrt n →
      ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * s)) * (1 / 8) * (2 / 3))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
      ∀ u v : EuclideanSpace ℝ (Fin n), u ∈ T → u ∈ K → v ∈ K → v ∉ T →
      ‖u - v‖ < δ / Real.sqrt n → densDist h u v < 1 / 4 →
      1 ≤ 20 * (speedyMetropolisGaussian K δ s u Tᶜ + speedyMetropolisGaussian K δ s v T) := by
  intro T hT u v _ huK hvK _ hsep _
  have hsep' : ‖v - u‖ < δ / Real.sqrt n := by rwa [norm_sub_rev]
  exact one_le_twenty_mul_speedyMetropolisGaussian_add_of_comparable hn hK hKc hδ hs hR
    huK hvK (hKR u huK) (hKR v hvK) hsep.le
    (volume_ball_inter_ne_zero_of_convex hKc hKb hK0 huK hδ)
    (max_volume_ball_inter_le_of_ell_comparable hδ (hcomp u huK v hvK hsep)
      (hcomp v hvK u huK hsep')) hfloor hT

/-! ## 4. `hmass`, and the composition -/

/-- **The `ℓ·γ`-weight of a bounded convex body of positive volume is non-zero.**  Both factors
of the density are strictly positive at every point of `K` — `ℓ` by
`Arlib.MarkovChains.volume_ball_inter_ne_zero_of_convex`, `γ` always — so the density is nowhere
zero on `K`, and a `lintegral` over a set of positive measure cannot vanish. -/
theorem ellGaussianMeasure_univ_ne_zero {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hK0 : volume K ≠ 0) {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    ellGaussianMeasure K δ s Set.univ ≠ 0 := by
  rw [ellGaussianMeasure_univ]
  intro hc
  rw [lintegral_eq_zero_iff (measurable_ell_mul_gaussianWeight hK δ s)] at hc
  have hsub : K ⊆ {x | ¬ ell K δ x * gaussianWeight s x = 0} := by
    intro x hx
    exact mul_ne_zero
      (ell_ne_zero_of_volume_ball_inter_ne_zero hδ
        (volume_ball_inter_ne_zero_of_convex hKc hKb hK0 hx hδ))
      (gaussianWeight_ne_zero s x)
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin n) |
      ¬ ell K δ x * gaussianWeight s x = 0} :=
    (measurable_ell_mul_gaussianWeight hK δ s (measurableSet_singleton 0)).compl
  have hzero : volume.restrict K {x | ¬ ell K δ x * gaussianWeight s x = 0} = 0 :=
    MeasureTheory.ae_iff.1 hc
  rw [Measure.restrict_apply hmeas, Set.inter_eq_self_of_subset_right hsub] at hzero
  exact hK0 hzero

/-- **`hmass`**: the unnormalised `ℓ·γ`-target of a bounded convex body of positive volume has
strictly positive total integral. -/
theorem integral_ellGaussianIndicator_pos {s : ℝ} (hs : 0 < s)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    0 < ∫ x, Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal s y) x := by
  have huniv := ellGaussianMeasure_eq_ofReal_setIntegral hs hK hKtop δ
    (MeasurableSet.univ (α := EuclideanSpace ℝ (Fin n)))
  rw [setIntegral_univ] at huniv
  have hne := ellGaussianMeasure_univ_ne_zero hK hKc hKb hK0 hδ s
  rw [huniv] at hne
  by_contra hcon
  exact hne (ENNReal.ofReal_eq_zero.2 (not_lt.1 hcon))

/-- **A conductance bound for `Arlib.MarkovChains.speedyMetropolisGaussian`** —
`Arlib.MarkovChains.conductance_speedyGaussian_ge` with every hypothesis it takes supplied for
this kernel, at `s = σ²`:

    Φ(speedyMetropolisGaussian K δ σ²)  ≥  δ·ln 2 / (640·σ·√n)

with respect to `Arlib.MarkovChains.ellGaussianProb K δ σ²`, which
`Arlib.MarkovChains.isReversible_speedyMetropolisGaussian_prob` shows is the chain's stationary
law.  The three obligations of `SpeedyGaussian.lean` §7 are discharged by
`hoverlap_speedyMetropolisGaussian`, `hpi_ellGaussian` and `hiso_speedyMetropolisGaussian`
respectively; `hmass` is `integral_ellGaussianIndicator_pos`.

**Two hypotheses remain, and this statement is conditional on them.  It is not a mixing-time
bound, not a spectral-gap bound and not a runtime claim, and may not be quoted as one.**

* `hcomp` — Cousins–Vempala's `d_ℓ(u,v) < 1/3` (`vol3_journal.tex:581`), as a *global* premise on
  `K` because `hoverlap`'s binder has no room for a per-pair one.  It is the same premise
  `Arlib.MarkovChains.overlap_speedyWalk_sqrt_of_ell_comparable_global` carries for the
  unfiltered speedy walk, and `Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample`
  shows it is a genuine restriction on `K`.
* `hellLip`/`hLσ` — log-Lipschitzness of `ℓ` on `K` at an explicit constant `Lf`, and its
  compatibility with `σ` and `R`.  These come from
  `Arlib.ellGaussian_isoperimetry_measurable_logTwo` and are **not** proved anywhere in this
  repository for a general convex body; see `hiso_speedyMetropolisGaussian`.

Everything else is discharged: measurability, convexity, boundedness (`hKR`), positive volume,
the acceptance floor (`acceptance_floor_of_cv`, from `hδσ` and `hRσ` alone), the local
non-degeneracy `ℓ > 0` (`ell_toReal_pos_of_convex`), reversibility, `π(Kᶜ) = 0` and `hmass`. -/
theorem conductance_speedyMetropolisGaussian_ge (hn : 2 ≤ n) {σ δ R Lf : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hLf : 0 ≤ Lf)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    (hcomp : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ < δ / Real.sqrt n →
      ell K δ x ≤ ENNReal.ofReal (3 / 2) * ell K δ y)
    (hellLip : ∀ u ∈ K, ∀ v ∈ K,
      (ell K δ u).toReal ≤ (ell K δ v).toReal * Real.exp (Lf * ‖u - v‖))
    (hLσ : Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance (speedyMetropolisGaussian K δ (σ ^ 2)) (ellGaussianProb K δ (σ ^ 2)) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  exact conductance_speedyGaussian_ge hn hσ hδ hδσ
    (fun x => Set.indicator_nonneg
      (fun y _ => mul_nonneg ENNReal.toReal_nonneg (gaussianWeightReal_pos _ y).le) x)
    (integral_ellGaussianIndicator_pos hs hK hKc hKb hK0 hKtop hδ)
    hK (speedyMetropolisGaussian K δ (σ ^ 2)) (ellGaussianProb K δ (σ ^ 2))
    (hpi_ellGaussian hs hK hKtop δ)
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    (ellGaussianProb_compl_eq_zero hK δ (σ ^ 2))
    (hoverlap_speedyMetropolisGaussian hn hK hKc hKb hK0 hδ hs hR hKR hcomp
      (acceptance_floor_of_cv hn hσ hδ hδσ hRσ) _)
    (hiso_speedyMetropolisGaussian hn hσ hδ hLf hK hKc hKb hKR hK0 hellLip hLσ)

end Arlib.MarkovChains

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Arlib.MarkovChains.ell_mul_gaussianWeight_eq_ofReal
#print axioms Arlib.MarkovChains.integrableOn_ell_mul_gaussianWeightReal
#print axioms Arlib.MarkovChains.ellGaussianMeasure_eq_ofReal_setIntegral
#print axioms Arlib.MarkovChains.hpi_ellGaussian
#print axioms Arlib.MarkovChains.ell_toReal_pos_of_convex
#print axioms Arlib.MarkovChains.hiso_speedyMetropolisGaussian
#print axioms Arlib.MarkovChains.mul_volume_le_speedyMetropolisGaussian
#print axioms Arlib.MarkovChains.one_le_twenty_mul_speedyMetropolisGaussian_add_of_comparable
#print axioms Arlib.MarkovChains.acceptance_floor_of_le
#print axioms Arlib.MarkovChains.acceptance_floor_of_cv
#print axioms Arlib.MarkovChains.hoverlap_speedyMetropolisGaussian
#print axioms Arlib.MarkovChains.ellGaussianMeasure_univ_ne_zero
#print axioms Arlib.MarkovChains.integral_ellGaussianIndicator_pos
#print axioms Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge
