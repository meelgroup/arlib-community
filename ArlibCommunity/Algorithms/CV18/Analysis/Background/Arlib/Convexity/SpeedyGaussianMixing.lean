/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.SpeedyGaussianUncond
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MixingSqrt
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.SpeedyWalk

/-!
# Cousins–Vempala `thm:mixing` for the lazy speedy Metropolis–Gaussian walk

`Arlib.conductance_speedyMetropolisGaussian_ge_uncond`
(`Arlib/Convexity/SpeedyGaussianUncond.lean:112`) is Cousins–Vempala's `thm:speedyconductance`
(`1409.6011/vol3_journal.tex:624`) with **no** isoperimetric and **no** comparability
hypothesis:

    Φ(speedyMetropolisGaussian K δ σ²)  ≥  δ·log 2 / (640·σ·√n)

with respect to `Arlib.MarkovChains.ellGaussianProb K δ σ²`.  Its module docstring says, in
capitals, that it is *not* a mixing time.  **This file supplies the missing step**: the
Lovász–Simonovits bound `thm:mixing` (`vol3_journal.tex:523`),

    d_tv(Q_t, Q)  ≤  √M · (1 − φ²/2)^t   for an `M`-warm `Q₀` and a **lazy** chain,

read as a step count and applied at that conductance.

## What is proved

| name | content |
|---|---|
| `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond` | `thm:mixing` at `φ = δ·log 2/(640·σ·√n)`, step count `4·(log M + 2·log(1/ε))/φ² + 1` |
| `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` | the same with `φ` substituted: `4·640²·σ²·n·(log M + 2·log(1/ε))/(δ·log 2)² + 1` |
| `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_witness` | every binder of both, discharged at concrete data, carrying the conclusion |

The step count is written out in both theorems; there is no `def` standing in for it.  Its
shape is `O(log(M/ε)/φ²) = O((σ√n/δ)²·log(M/ε))`, which is the Lovász–Simonovits shape.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.

## Why the chain is `lazy`

`thm:mixing` is stated by Lovász–Simonovits (and quoted by Cousins–Vempala) for a **lazy**
chain, and that word is load-bearing: without a spectral hypothesis the bound is false, and
`Arlib/MarkovChains/Continuous/ConductanceToTV.lean:229–243` records the counterexample (the
swap kernel on `Bool`, reversible with `Φ = 1`, whose total variation never decays).  Laziness
is exactly what buys the missing hypothesis: `Arlib.MarkovChains.hasNonnegSpectrum_lazy`
proves `HasNonnegSpectrum (lazy P) π` from reversibility of `P` alone, and
`Arlib.MarkovChains.conductance_lazy` prices it at a factor `2` in the conductance — hence the
factor `4` in the step count.  Nothing in this repository proves a spectral property of the
plain `speedyMetropolisGaussian` kernel, so no plain-chain variant is stated here.

## Which hypotheses are discharged, and which are added

**Discharged inside**, so that they are not binders:

* `IsMarkovKernel (speedyMetropolisGaussian K δ σ²)` — instance
  `Arlib.MarkovChains.isMarkovKernel_speedyMetropolisGaussian`;
* `IsReversible (speedyMetropolisGaussian K δ σ²) (ellGaussianProb K δ σ²)` —
  `Arlib.MarkovChains.isReversible_speedyMetropolisGaussian_prob`, which needs only `hK`;
* `IsProbabilityMeasure (ellGaussianProb K δ σ²)` —
  `Arlib.MarkovChains.isProbabilityMeasure_ellGaussianProb` with its two guards from
  `ellGaussianMeasure_univ_ne_zero` and `ellGaussianMeasure_univ_le`;
* `(SmallSets (ellGaussianProb K δ σ²) (1/2)).Nonempty` —
  `Arlib.MarkovChains.exists_smallSet_of_absolutelyContinuous` at
  `ellGaussianProb_absolutelyContinuous`;
* `Bornology.IsBounded K` and `volume K ≠ ⊤` — derived from `hR`/`hKR` exactly as the
  conductance theorem derives them, so they cost no binder.

**Added** beyond the binders of `conductance_speedyMetropolisGaussian_ge_uncond`: only the
warm start and the accuracy, namely `{mu0} [IsProbabilityMeasure mu0] {M eps}`, `hM : 1 ≤ M`,
`hwarm : IsWarm (ofReal M) mu0 (ellGaussianProb K δ σ²)`, `heps0 : 0 < eps`,
`heps1 : eps ≤ 1`, and `{t}` with the step-count hypothesis `ht`.  The warm start is
`thm:mixing`'s own hypothesis and no mixing theorem can drop it (a point mass never mixes in a
bounded number of steps under a fixed bound); it is **not** proved here, as instructed.

## Scope — read before quoting

The target is `Arlib.MarkovChains.ellGaussianProb K δ σ²`, the **speedy chain's own stationary
law** `∝ 1_K·ℓ·e^{−‖x‖²/2σ²}`, not the Gaussian restricted to `K`.  The speedy-to-target
transfer (`SpeedyToUniform.lean`, `HoldingTime.lean`) is a separate step and is **not**
performed here, so this is not a sampler for the Gaussian-tilted uniform law and not a
statement about the Cousins–Vempala volume algorithm.

It is also **not a running-time statement**: the conclusion is `MixesWithin`, a bound on the
total variation distance of the law after `t` steps.  No count of arithmetic operations,
oracle calls or samples appears in it, and the step count must not be quoted as one; the cost
of a single speedy step (a rejection loop) is not bounded anywhere below.
-/

namespace Arlib

open MeasureTheory Arlib.MarkovChains

variable {n : ℕ}

/-! ## 1. The mixing bound

`Arlib.MarkovChains.mixesWithin_lazy_of_conductance_sqrt` (`MixingSqrt.lean:294`) is
`thm:mixing` read as a step count at a conductance of exactly the shape
`δ·log 2/(640·σ·√n)`, for `lazy P` with `P` reversible.  Its `hΦ` slot is, character for
character, the conclusion of `Arlib.conductance_speedyMetropolisGaussian_ge_uncond`; the two
compose by `exact`. -/

/-- **Cousins–Vempala `thm:mixing` for the lazy speedy Metropolis–Gaussian walk.**

For `n ≥ 21`, a measurable convex `K ⊆ ℝⁿ` of positive volume inside the ball of radius
`R ≤ 2σ√n`, and a step `0 < δ ≤ σ/(8√n)`, the **lazy** chain
`lazy (speedyMetropolisGaussian K δ σ²)` started from an `M`-warm `mu0` is within total
variation `ε` of `ellGaussianProb K δ σ²` after

    4·(log M + 2·log(1/ε)) / (δ·log 2/(640·σ·√n))² + 1

steps — the Lovász–Simonovits count `O(log(M/ε)/φ²)` at the conductance
`φ = δ·log 2/(640·σ·√n)` that `Arlib.conductance_speedyMetropolisGaussian_ge_uncond`
certifies, with the factor `4` that laziness costs.

Its binders are those of `Arlib.conductance_speedyMetropolisGaussian_ge_uncond` plus the
warm-start data and the accuracy; see the module docstring.  No isoperimetric, comparability
or spectral hypothesis appears.

`Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` is the same statement with
`φ` substituted, which is where the `O((σ√n/δ)²·log(M/ε))` shape is visible.

**This is not a running-time statement, and the target is the speedy chain's own stationary
law.**  See the module docstring. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_uncond (hn : 21 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M) (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2))) (ellGaussianProb K δ (σ ^ 2))
      mu0 t (ENNReal.ofReal eps) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  haveI : IsProbabilityMeasure (ellGaussianProb K δ (σ ^ 2)) :=
    isProbabilityMeasure_ellGaussianProb
      (ellGaussianMeasure_univ_ne_zero hK hKc hKb hK0 hδ (σ ^ 2))
      (ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hs K δ))
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ :=
    exists_smallSet_of_absolutelyContinuous (n := n) (by omega) (ellGaussianProb K δ (σ ^ 2))
      (ellGaussianProb_absolutelyContinuous K δ (σ ^ 2))
  exact mixesWithin_lazy_of_conductance_sqrt (by omega) hσ hδ hδσ
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    ⟨S0, hS0m, hS0pos, hS0half⟩ hM hwarm heps0 heps1
    (conductance_speedyMetropolisGaussian_ge_uncond hn hσ hδ hδσ hK hKc hK0 hR hKR hRσ) ht

/-- **The same step count with the conductance substituted.**

`(δ·log 2/(640·σ·√n))² = (δ·log 2)²/(640²·σ²·n)`, so the deadline of
`Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond` is

    4·640²·σ²·n·(log M + 2·log(1/ε)) / (δ·log 2)² + 1,

which is the `O((σ√n/δ)²·log(M/ε))` shape of the Lovász–Simonovits bound.  Only the spelling
of the deadline changes; every binder and the conclusion are those of that theorem. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit (hn : 21 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M) (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2) ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2))) (ellGaussianProb K δ (σ ^ 2))
      mu0 t (ENNReal.ofReal eps) := by
  refine mixesWithin_lazy_speedyMetropolisGaussian_uncond hn hσ hδ hδσ hK hKc hK0 hR hKR hRσ
    hM hwarm heps0 heps1 ?_
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have heq : 4 * ((Real.log M + 2 * Real.log (1 / eps))
        / (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2)
      = 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
        / (δ * Real.log 2) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, hsq, div_div_eq_mul_div]
    field_simp
  rw [heq]
  exact ht

/-! ## 2. Non-vacuity (`CLAUDE.md` §11)

`Arlib.conductance_speedyMetropolisGaussian_ge_uncond_witness`
(`Arlib/Convexity/SpeedyGaussianUncond.lean:161`) discharges the conductance theorem's whole
binder bundle at

    n = 21,  K = B̄(0,1),  σ = 100,  δ = 1,  R = 1.

The witness below is that one **extended** by the warm start and the accuracy: `mu0 = π` (the
stationary start, the smallest legal warm-start datum, `M = 1`), `ε = 1/2` — so the conclusion
is a genuine `1/2` bound and not the trivial `ε = 1` one — and an explicit step count
`t = 2·10¹²`, which clears the deadline

    4·640²·100²·21·(log 1 + 2·log 2)/(1·log 2)² + 1 = 688128000000/log 2 + 1 ≈ 9.93·10¹¹

because `log 2 > 0.6931471803` (`Real.log_two_gt_d9`).  Both spellings of the deadline are
carried, so the witness serves both theorems of §1. -/

/-- **Non-vacuity: every binder of both theorems of §1, discharged simultaneously at concrete
data, with the `MixesWithin` conclusion carried as the last conjunct.**

    n = 21,  K = B̄(0,1) ⊆ ℝ²¹,  σ = 100,  δ = 1,  R = 1,
    mu0 = ellGaussianProb K δ σ²,  M = 1,  ε = 1/2,  t = 2·10¹².

The geometric half is `Arlib.conductance_speedyMetropolisGaussian_ge_uncond_witness`'s:
`1 ≤ 100/(8√21)` since `√21 ≤ 5`, and `1 ≤ 200√21` with enormous room.  The warm start is the
stationary one — `IsWarm (ofReal 1) π π` is `Arlib.IsWarm.refl` — which is legitimate exactly
because `π = ellGaussianProb K 1 100²` really is a probability measure here
(`isProbabilityMeasure_ellGaussianProb`, whose guards a bounded convex `K` of positive volume
supplies).

Since the theorems of §1 carry no isoperimetric, comparability or spectral binder, nothing is
left over: this is an *unconditional* instance. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_uncond_witness :
    ∃ (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m))) (σ δ R : ℝ)
      (mu0 : Measure (EuclideanSpace ℝ (Fin m))) (M eps : ℝ) (t : ℕ),
      21 ≤ m ∧ 0 < σ ∧ 0 < δ ∧ δ ≤ σ / (8 * Real.sqrt m) ∧
      MeasurableSet K ∧ Convex ℝ K ∧ volume K ≠ 0 ∧ 0 ≤ R ∧
      (∀ x ∈ K, ‖x‖ ≤ R) ∧ R ≤ 2 * σ * Real.sqrt m ∧
      IsProbabilityMeasure mu0 ∧ 1 ≤ M ∧
      IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K δ (σ ^ 2)) ∧
      0 < eps ∧ eps ≤ 1 ∧ eps < 1 ∧
      4 * ((Real.log M + 2 * Real.log (1 / eps))
        / (δ * Real.log 2 / (640 * σ * Real.sqrt m)) ^ 2) + 1 ≤ (t : ℝ) ∧
      4 * 640 ^ 2 * σ ^ 2 * (m : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
        / (δ * Real.log 2) ^ 2 + 1 ≤ (t : ℝ) ∧
      MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2))) (ellGaussianProb K δ (σ ^ 2))
        mu0 t (ENNReal.ofReal eps) := by
  classical
  have hcast : Real.sqrt ((21 : ℕ) : ℝ) = Real.sqrt (21 : ℝ) := by norm_num
  have hnn : (0 : ℝ) ≤ Real.sqrt (21 : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (21 : ℝ) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h4 : (4 : ℝ) ≤ Real.sqrt (21 : ℝ) := by nlinarith
  have h5 : Real.sqrt (21 : ℝ) ≤ 5 := by nlinarith
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlogpos
  have hlog9 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  set K : Set (EuclideanSpace ℝ (Fin 21)) := Metric.closedBall 0 1 with hKdef
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hKc : Convex ℝ K := convex_closedBall _ _
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall
  have hKtop : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hK0 : volume K ≠ 0 := by
    have : 0 < volume K :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by norm_num : (0 : ℝ) < 1))
        (measure_mono Metric.ball_subset_closedBall)
    exact this.ne'
  have hKR : ∀ x ∈ K, ‖x‖ ≤ 1 := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hδσ : (1 : ℝ) ≤ 100 / (8 * Real.sqrt ((21 : ℕ) : ℝ)) := by
    rw [hcast, le_div_iff₀ (by positivity)]
    linarith
  have hRσ : (1 : ℝ) ≤ 2 * 100 * Real.sqrt ((21 : ℕ) : ℝ) := by
    rw [hcast]; linarith
  have hs : (0 : ℝ) < (100 : ℝ) ^ 2 := by norm_num
  haveI hprob : IsProbabilityMeasure (ellGaussianProb K (1 : ℝ) ((100 : ℝ) ^ 2)) :=
    isProbabilityMeasure_ellGaussianProb
      (ellGaussianMeasure_univ_ne_zero hKm hKc hKb hK0 (by norm_num) ((100 : ℝ) ^ 2))
      (ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hs K 1))
  have hwarm : IsWarm (ENNReal.ofReal (1 : ℝ)) (ellGaussianProb K (1 : ℝ) ((100 : ℝ) ^ 2))
      (ellGaussianProb K (1 : ℝ) ((100 : ℝ) ^ 2)) := by
    intro S _
    exact le_of_eq (by rw [ENNReal.ofReal_one, one_mul])
  -- the deadline, in the substituted spelling, at `M = 1`, `ε = 1/2`
  have hdead : 4 * 640 ^ 2 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ))
        * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / ((1 : ℝ) * Real.log 2) ^ 2 + 1
      ≤ ((2000000000000 : ℕ) : ℝ) := by
    have hone : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
    have hkey : 4 * 640 ^ 2 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ))
          * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / ((1 : ℝ) * Real.log 2) ^ 2
        = 688128000000 / Real.log 2 := by
      rw [Real.log_one, hone]
      push_cast
      field_simp
      ring
    have hquot : 688128000000 / Real.log 2 ≤ 999999999999 := by
      rw [div_le_iff₀ hlogpos]
      nlinarith
    rw [hkey]
    push_cast
    linarith
  -- the two spellings of the deadline agree
  have hsq21 : Real.sqrt ((21 : ℕ) : ℝ) ^ 2 = ((21 : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg 21)
  have hdead' : 4 * ((Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ)))
        / ((1 : ℝ) * Real.log 2 / (640 * 100 * Real.sqrt ((21 : ℕ) : ℝ))) ^ 2) + 1
      ≤ ((2000000000000 : ℕ) : ℝ) := by
    have heq : 4 * ((Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ)))
          / ((1 : ℝ) * Real.log 2 / (640 * 100 * Real.sqrt ((21 : ℕ) : ℝ))) ^ 2)
        = 4 * 640 ^ 2 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ))
          * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / ((1 : ℝ) * Real.log 2) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, hsq21, div_div_eq_mul_div]
      field_simp
    rw [heq]
    exact hdead
  have hmix : MixesWithin (lazy (speedyMetropolisGaussian K (1 : ℝ) ((100 : ℝ) ^ 2)))
      (ellGaussianProb K (1 : ℝ) ((100 : ℝ) ^ 2))
      (ellGaussianProb K (1 : ℝ) ((100 : ℝ) ^ 2)) 2000000000000
      (ENNReal.ofReal (1 / 2)) :=
    mixesWithin_lazy_speedyMetropolisGaussian_uncond (n := 21) (σ := 100) (δ := 1) (R := 1)
      (M := 1) (eps := 1 / 2) le_rfl (by norm_num) (by norm_num) hδσ hKm hKc hK0 (by norm_num)
      hKR hRσ le_rfl hwarm (by norm_num) (by norm_num) hdead'
  exact ⟨21, K, 100, 1, 1, ellGaussianProb K (1 : ℝ) ((100 : ℝ) ^ 2), 1, 1 / 2,
    2000000000000, le_rfl, by norm_num, by norm_num, hδσ, hKm, hKc, hK0, by norm_num, hKR,
    hRσ, hprob, le_rfl, hwarm, by norm_num, by norm_num, by norm_num, hdead', hdead, hmix⟩

/-! ### Axiom audit (`CLAUDE.md` §4) -/

section AxiomCheck

#print axioms Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond
#print axioms Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit
#print axioms Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_witness

end AxiomCheck

end Arlib
