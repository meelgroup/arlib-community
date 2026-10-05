/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.MetropolisConductanceSharp
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.OverlapSqrt

/-!
# The step-size cap: which `δ` the conductance route actually runs at

Two conductance bounds for the speedy walk on a convex body sit in this library, and they look
like they disagree about a factor `√n`:

| theorem | cap | bound |
|---|---|---|
| `Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex` (`StarPolar.lean:626`) | `δ ≤ σ/8` | `δ·ln 2/(640·σ·n)` |
| `Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell_comparable` (`OverlapSqrt.lean:658`) | `δ ≤ σ/(8√n)` | `δ·ln 2/(640·σ·√n)` |

Taking each at *its own* maximal `δ` gives the same number, `ln 2/(5120·n)`
(`sup_bounds_agree_at_own_caps`), which makes the `√n` look illusory.  This file establishes
that the appearance is an artifact of that comparison, and that the `√n` is real.

## 1. They are one theorem at two parameterizations

`Arlib.MarkovChains.conductance_speedyGaussian_ge` (`SpeedyConductanceSharp.lean:320`) takes the
kernel `P` as a **parameter independent of its own `δ`**.  So that `δ` is an *isoperimetric
scale*, not a step size.

* `StarPolar.lean:664–666` instantiates it at `δ_abs := δ/√n` with kernel `speedyWalk K δ`;
  the cap `δ_abs ≤ σ/(8√n)` becomes `δ ≤ σ/8` (`speedyGaussian_reparam_cap`) and the
  conclusion becomes `δ·ln 2/(640σn)` (`speedyGaussian_reparam_conclusion`).
* `OverlapSqrt.lean:679` instantiates the *same* theorem at `δ_abs := δ` with the *same*
  kernel `speedyWalk K δ`.

Neither shrank any cap; both inherited `hδσ` from the abstract theorem.  What differs is the
overlap lemma each can supply: `overlap_speedyWalk_convex` gives overlap only at separation
`δ/n`, whereas `overlap_speedyWalk_sqrt_of_ell_comparable_global` gives it at `δ/√n` — at the
price of `ℓ`-comparability.

## 2. At a fixed kernel step the gain is real, and the step is not free

For one and the same kernel `speedyWalk K δ`, the second bound is exactly `√n` times the first
(`speedy_sqrt_gain`).  The operative question is therefore *which `δ` the algorithm runs at*,
and that is set by the Metropolis acceptance floor, not by these caps.

`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`
(`MetropolisConductanceSharp.lean:431`) carries

    hfloor : 1 ≤ 20·exp(−(2Rδ + δ²)/(2σ²))·(1 − 1/n)ⁿ·θ.

`metropolis_hfloor_forces_step_cap` shows that, using only hypotheses that theorem already
makes plus `σ√n ≤ R`, `hfloor` **forces** `δ ≤ (ln 20)·σ/√n ≈ 3σ/√n`.  The mechanism is
`acceptance_floor_exp_small_of_large_step`: for `R ≥ σ√n` the acceptance factor is at most
`e^{−δ√n/σ}`, so at the nominal cap `δ = σ/8` it is `e^{−√n/8}`
(`acceptance_floor_at_step_sigma_div_eight`) — exponentially small in `n`, and no `θ ≤ 1` can
compensate.  Conversely at `δ ≤ σ/(8√n)` (and `R ≤ σ√n`) the factor is at least `e^{−1/4}`
(`acceptance_factor_ge_of_step_le`), so `σ/√n` is exactly the right scale.

Evaluated at that operative step `δ = σ/(8√n)`:

    (old)  Φ ≥ ln 2/(5120·n^{3/2})     `speedy_old_bound_at_operative_step`
    (new)  Φ ≥ ln 2/(5120·n)           `speedy_new_bound_at_operative_step`

A genuine factor `√n` in `Φ`, hence a factor `n` in the step count `1/Φ²`.  **The step-size cap
is not the obstruction.**

## 3. A separate finding: `hδσ`'s `√n` is itself removable

`hδσ` is consumed at exactly two places in `conductance_speedyGaussian_ge`
(`SpeedyConductanceSharp.lean:367` and `:489`), both purely arithmetic, and in both the `√n`
cancels: the quantity bounded is `4(d/σ)√n = 4δ·ln 2/σ` at `d = δ·ln 2/√n`.  Its real content
is the dimension-free `16·(ln 2)·δ ≤ σ` (`isoStep_quarter_iff`), and both side conditions
follow from `δ ≤ σ/12` (`four_mul_isoStep_div_sigma_le_quarter_of_dimension_free`,
`isoStep_conductance_le_inv_160_of_dimension_free`).  The constant is *not* free, though:
`δ ≤ σ/8` genuinely fails (`not_isoStep_quarter_at_sigma_div_eight`), the honest cap being
`σ/(16 ln 2) ≈ σ/11.09`.

This file does **not** re-prove `conductance_speedyGaussian_ge` with the weaker binder —
that means editing `SpeedyConductanceSharp.lean`, which this file does not own — and no
declaration here claims the relaxed theorem.  It is also not needed for §2: the operative step
`Θ(σ/√n)` is well inside the existing cap.

## 4. What still blocks cashing the `√n` for the real algorithm

Two things, both hypotheses rather than caps.

* **The `δ/√n` overlap lemma exists only for the unfiltered speedy walk.**
  `Arlib.MarkovChains.metropolisGaussian_overlap_of_convex`
  (`MetropolisConductanceSharp.lean:238`) concludes only for pairs at separation `δ/n`
  (`:247`), which is why the sharp Metropolis theorem is stated at `δ_abs = δ/√n` and lands on
  `δ·ln 2/(640σn)`.  A Metropolis overlap lemma at separation `δ/√n` is the named missing
  piece; it is the analogue of `overlap_speedyWalk_sqrt_of_ell_comparable_global` for the
  filtered kernel.
* **`hcomp` and `hiso` remain hypotheses.**  `ℓ`-comparability at separation `δ/√n` is
  Cousins–Vempala's own hypothesis but is *not* automatic on every convex body — see
  `Arlib.MarkovChains.exists_ell_not_comparable_at_sqrt_dim_counterexample`
  (`OverlapSqrt.lean:805`).  `thm:iso` (`hiso`) is unproved throughout this repository.

**Nothing in this file is a mixing-time or polynomial-time statement, and none of it may be
quoted as one.**
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## 1. The operative step size is forced to `O(σ/√n)` by the acceptance floor -/

/-- **The Metropolis acceptance floor forces `δ = O(σ/√n)` in the Cousins–Vempala regime.**

`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge` carries the hypothesis

    hfloor : 1 ≤ 20·exp(−(2Rδ + δ²)/(2σ²))·(1 − 1/n)ⁿ·θ

together with `hell : ∀ x ∈ K, θ ≤ ℓ(x)` and `hK0 : vol K ≠ 0`.  Those last two already pin
`θ ≤ 1` (local conductance is a probability, `Arlib.MarkovChains.ell_le_one`), and
`(1 − 1/n)ⁿ ≤ 1`, so `hfloor` forces `20·exp(−(2Rδ + δ²)/(2σ²)) ≥ 1`, i.e.

    (2Rδ + δ²)/(2σ²) ≤ ln 20.

In the Cousins–Vempala regime the body has radius `R ≍ σ√n`; assuming only the lower half of
that (`σ√n ≤ R`) and dropping `δ² ≥ 0` gives `σ√n·δ ≤ σ²·ln 20`, i.e.

    δ ≤ (ln 20)·σ/√n   (`ln 20 ≈ 2.996`).

**This is the operative step size.**  It is *not* an artifact of how the conductance theorems
state their caps: no instantiation of the sharp Metropolis theorem with a step larger than
`3σ/√n` can have a satisfiable `hfloor` once `R ≥ σ√n`.  Every hypothesis used here is one the
sharp theorem already assumes — nothing extra is imposed beyond `σ√n ≤ R`. -/
theorem metropolis_hfloor_forces_step_cap {n : ℕ} (hn : 2 ≤ n) {σ δ R θ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK0 : volume K ≠ 0)
    (hCV : σ * Real.sqrt n ≤ R)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))
      * (1 - 1 / (n : ℝ)) ^ n * θ) :
    δ ≤ Real.log 20 * σ / Real.sqrt n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- `θ ≤ 1`: the floor is a lower bound for a local conductance, which is a probability
  obtain ⟨x0, hx0⟩ := nonempty_of_measure_ne_zero hK0
  have hθ1 : θ ≤ 1 := ENNReal.ofReal_le_one.1 ((hell x0 hx0).trans (ell_le_one K δ x0))
  have hp0 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
    linarith
  have hppow : (0 : ℝ) < (1 - 1 / (n : ℝ)) ^ n := pow_pos hp0 n
  have hppow1 : (1 - 1 / (n : ℝ)) ^ n ≤ 1 := by
    refine pow_le_one₀ hp0.le ?_
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith
  have hexp : (0 : ℝ) < Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) := Real.exp_pos _
  -- `θ ≥ 0`: otherwise the floor's right-hand side is negative
  have hpos20 : (0 : ℝ) < 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))
      * (1 - 1 / (n : ℝ)) ^ n :=
    mul_pos (mul_pos (by norm_num) hexp) hppow
  have hθ0 : (0 : ℝ) ≤ θ := by
    by_contra hc
    push Not at hc
    have := mul_neg_of_pos_of_neg hpos20 hc
    linarith
  -- discard the two factors that are at most `1`
  have hpt : (1 - 1 / (n : ℝ)) ^ n * θ ≤ 1 := by nlinarith
  have h20 : (1 : ℝ) / 20 ≤ Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) := by
    nlinarith [mul_nonneg hexp.le (by linarith : (0 : ℝ) ≤ 1 - (1 - 1 / (n : ℝ)) ^ n * θ)]
  -- invert the exponential
  have hlog : Real.log (1 / 20) ≤ -(2 * R * δ + δ ^ 2) / (2 * σ ^ 2) :=
    (Real.log_le_iff_le_exp (by norm_num)).2 h20
  rw [one_div, Real.log_inv] at hlog
  have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity
  have hAB : (2 * R * δ + δ ^ 2) / (2 * σ ^ 2) ≤ Real.log 20 := by
    rw [neg_div] at hlog
    linarith
  have hkey : 2 * R * δ + δ ^ 2 ≤ Real.log 20 * (2 * σ ^ 2) := (div_le_iff₀ hσ2).1 hAB
  rw [le_div_iff₀ hsq]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ R - σ * Real.sqrt n) hδ.le, sq_nonneg δ]

/-- **The acceptance factor is exponentially small once `δ ≫ σ/√n`.**  For a body of radius
`R ≥ σ√n` (the Cousins–Vempala regime),

    exp(−(2Rδ + δ²)/(2σ²))  ≤  exp(−δ√n/σ).

So the factor decays like `e^{−δ√n/σ}`: it is `Θ(1)` exactly while `δ = O(σ/√n)`, and
exponentially small in `n` beyond that. -/
theorem acceptance_floor_exp_small_of_large_step {n : ℕ} {σ δ R : ℝ} (hσ : 0 < σ)
    (hδ : 0 ≤ δ) (hCV : σ * Real.sqrt n ≤ R) :
    Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) ≤ Real.exp (-(δ * Real.sqrt n / σ)) := by
  refine Real.exp_le_exp.2 ?_
  rw [neg_div]
  have hle : δ * Real.sqrt n / σ ≤ (2 * R * δ + δ ^ 2) / (2 * σ ^ 2) := by
    rw [div_le_div_iff₀ hσ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ R - σ * Real.sqrt n) hδ) hσ.le,
      mul_nonneg (sq_nonneg δ) hσ.le]
  linarith

/-- **At the step `δ = σ/8` the acceptance factor is `e^{−√n/8}`.**  The instance of
`acceptance_floor_exp_small_of_large_step` at the step size
`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_ge`'s own cap `δ ≤ σ/8` permits: in
the Cousins–Vempala regime the acceptance factor there is exponentially small in `n`.

The claim is asymptotic, not universal: `metropolis_hfloor_forces_step_cap` rules `δ = σ/8`
out only once `σ/8 > (ln 20)σ/√n`, i.e. once `√n > 8 ln 20 ≈ 23.97`, i.e. for `n ≥ 575`.
Below that the nominal cap is still inside the forced one. -/
theorem acceptance_floor_at_step_sigma_div_eight {n : ℕ} {σ R : ℝ} (hσ : 0 < σ)
    (hCV : σ * Real.sqrt n ≤ R) :
    Real.exp (-(2 * R * (σ / 8) + (σ / 8) ^ 2) / (2 * σ ^ 2))
      ≤ Real.exp (-(Real.sqrt n / 8)) := by
  refine le_trans (acceptance_floor_exp_small_of_large_step hσ (by positivity) hCV) ?_
  refine Real.exp_le_exp.2 ?_
  have h8 : σ / 8 * Real.sqrt n / σ = Real.sqrt n / 8 := by field_simp
  rw [h8]

/-- **At `δ ≤ σ/(8√n)` the acceptance factor is a constant.**  If moreover `R ≤ σ√n` (the
upper half of the Cousins–Vempala regime), then

    exp(−(2Rδ + δ²)/(2σ²))  ≥  e^{−1/4}  ≈  0.78.

Together with `metropolis_hfloor_forces_step_cap` this pins the scale exactly: the acceptance
factor is `Θ(1)` for `δ ≲ σ/√n` and the floor is unsatisfiable for `δ ≳ 3σ/√n`.

**This bounds only the exponential factor of `hfloor`, not `hfloor` itself**: satisfying
`1 ≤ 20·exp(…)·(1 − 1/n)ⁿ·θ` also needs a local-conductance floor `θ` bounded away from `0`
on the body, which is a separate (and genuinely restrictive) condition. -/
theorem acceptance_factor_ge_of_step_le {n : ℕ} (hn : 2 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ)
    (hδ0 : 0 ≤ δ) (hR : R ≤ σ * Real.sqrt n)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) :
    Real.exp (-(1 / 4)) ≤ Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at this
  have hδ' : δ * (8 * Real.sqrt n) ≤ σ := by
    rw [le_div_iff₀ (by positivity)] at hδσ
    linarith
  -- `√n·δ ≤ σ/8`, hence `2Rδ ≤ σ²/4`; and `δ ≤ σ/8`, hence `δ² ≤ σ²/64`
  have hsδ : Real.sqrt n * δ ≤ σ / 8 := by nlinarith
  have hδσ8 : δ ≤ σ / 8 := by nlinarith
  refine Real.exp_le_exp.2 ?_
  rw [neg_div]
  have hle : (2 * R * δ + δ ^ 2) / (2 * σ ^ 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hR hδ0, mul_le_mul_of_nonneg_left hsδ hσ.le,
      mul_le_mul_of_nonneg_right hδσ8 hδ0]
  linarith

/-! ## 2. The two conductance theorems are one theorem at two parameterizations -/

/-- **`conductance_speedyWalk_ge_of_convex`'s conclusion is the abstract one at `δ/√n`.**

`Arlib.MarkovChains.conductance_speedyGaussian_ge` takes the kernel `P` as a *parameter*
independent of its own `δ`, so `δ` there is an isoperimetric scale, not a step size.
`Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex` (`StarPolar.lean:626`) instantiates it
at `δ_abs := δ/√n` while keeping the kernel `speedyWalk K δ`
(`StarPolar.lean:664–666`), and this identity is why its printed conclusion reads
`δ·ln 2/(640σn)`.  `Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell_comparable`
(`OverlapSqrt.lean:658`) instantiates the *same* abstract theorem at `δ_abs := δ`
(`OverlapSqrt.lean:679`). -/
theorem speedyGaussian_reparam_conclusion {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ) :
    δ / Real.sqrt n * Real.log 2 / (640 * σ * Real.sqrt n)
      = δ * Real.log 2 / (640 * σ * (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  have h1 : δ / Real.sqrt n * Real.log 2 / (640 * σ * Real.sqrt n)
      = δ * Real.log 2 / (640 * σ * (Real.sqrt n * Real.sqrt n)) := by
    field_simp
  rw [h1, hsq]

/-- **The two caps are the same cap at the two parameterizations.**  `δ ≤ σ/8` for the kernel
step is *exactly* `δ_abs ≤ σ/(8√n)` for the abstract parameter `δ_abs = δ/√n`.  So
`Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell_comparable` did not shrink any cap:
it inherited the abstract theorem's cap and reads it at a different parameter. -/
theorem speedyGaussian_reparam_cap {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} :
    δ / Real.sqrt n ≤ σ / (8 * Real.sqrt n) ↔ δ ≤ σ / 8 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  rw [div_le_div_iff₀ hspos (by positivity), le_div_iff₀ (by norm_num : (0:ℝ) < 8)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **At a fixed kernel step `δ`, the `δ/√n`-overlap route is `√n` better.**

    (old)  Φ(speedyWalk K δ)  ≥  δ·ln 2/(640·σ·n)          `StarPolar.lean:626`
    (new)  Φ(speedyWalk K δ)  ≥  δ·ln 2/(640·σ·√n)         `OverlapSqrt.lean:658`

and the second is exactly `√n` times the first.  Same kernel, same step, same `σ`.  The gain
is entirely the better overlap lemma: `overlap_speedyWalk_convex` supplies overlap only at
separation `δ/n`, while `overlap_speedyWalk_sqrt_of_ell_comparable_global` supplies it at
`δ/√n` — at the price of the `ℓ`-comparability hypothesis `hcomp`. -/
theorem speedy_sqrt_gain {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ) :
    δ * Real.log 2 / (640 * σ * (n : ℝ)) * Real.sqrt n
      = δ * Real.log 2 / (640 * σ * Real.sqrt n) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  calc δ * Real.log 2 / (640 * σ * (n : ℝ)) * Real.sqrt n
      = δ * Real.log 2 / (640 * σ * (Real.sqrt n * Real.sqrt n)) * Real.sqrt n := by rw [hsq]
    _ = δ * Real.log 2 / (640 * σ * Real.sqrt n) := by field_simp

/-! ## 3. The two bounds at the operative step `δ = σ/(8√n)` -/

/-- **The old bound at the operative step.**  The certified constant of
`Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex`, evaluated at `δ = σ/(8√n)`, equals
`ln 2/(5120·n^{3/2})`.  (An identity between reals; the conductance inequality is that
theorem's, not this one's.) -/
theorem speedy_old_bound_at_operative_step {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    σ / (8 * Real.sqrt n) * Real.log 2 / (640 * σ * (n : ℝ))
      = Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  field_simp
  ring

/-- **The new bound at the operative step.**  The certified constant of
`Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell_comparable`, evaluated at
`δ = σ/(8√n)`, equals `ln 2/(5120·n)` — a factor `√n` better than
`speedy_old_bound_at_operative_step`.  (An identity between reals; the conductance inequality
is that theorem's, not this one's.)

`metropolis_hfloor_forces_step_cap` pins the algorithm's step at `δ = Θ(σ/√n)`, which is
*inside* both theorems' caps.  Evaluated there, the `δ/√n`-overlap route gives `Ω(1/n)` where
the `δ/n` route gives `Ω(n^{-3/2})`.  Since mixing time goes as `1/Φ²`, that is a factor `n`
in the step count. -/
theorem speedy_new_bound_at_operative_step {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    σ / (8 * Real.sqrt n) * Real.log 2 / (640 * σ * Real.sqrt n)
      = Real.log 2 / (5120 * (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  calc σ / (8 * Real.sqrt n) * Real.log 2 / (640 * σ * Real.sqrt n)
      = Real.log 2 / (5120 * (Real.sqrt n * Real.sqrt n)) := by field_simp; ring
    _ = Real.log 2 / (5120 * (n : ℝ)) := by rw [hsq]

/-- **Why the "sup over `δ`" comparison is the wrong test.**  Each theorem, evaluated at *its
own* maximal `δ`, gives the same number `ln 2/(5120·n)`:

    (old)  at `δ = σ/8`:      (σ/8)·ln 2/(640·σ·n)   = ln 2/(5120·n)
    (new)  at `δ = σ/(8√n)`:  (σ/(8√n))·ln 2/(640·σ·√n) = ln 2/(5120·n)

This identity — verified numerically at `n = 2, 10, 100, 10000` before it was proved — is
real, and it is what made the `√n` look illusory.  But it compares the two theorems at
*different kernels* (step `σ/8` versus step `σ/(8√n)`), and the algorithm does not get to
choose: `metropolis_hfloor_forces_step_cap` forces `δ = O(σ/√n)`.  At that common step the
new bound is `√n` better (`speedy_sqrt_gain`). -/
theorem sup_bounds_agree_at_own_caps {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    σ / 8 * Real.log 2 / (640 * σ * (n : ℝ))
      = σ / (8 * Real.sqrt n) * Real.log 2 / (640 * σ * Real.sqrt n) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  rw [speedy_new_bound_at_operative_step hn hσ]
  field_simp
  ring

/-! ## 4. Where `hδσ` is consumed, the cap is dimension-free

`hδσ : δ ≤ σ/(8√n)` is consumed at exactly **two** places inside
`Arlib.MarkovChains.conductance_speedyGaussian_ge`:

* `SpeedyConductanceSharp.lean:367` — via `isoStep_conductance_le_inv_160`, to know the
  certified constant never exceeds the degenerate branch's `1/160`;
* `SpeedyConductanceSharp.lean:489` — via `four_mul_isoStep_div_sigma_le_quarter`, to know
  `thm:iso`'s density branch sits under `cor:overlap`'s threshold `1/4`.

Both are pure arithmetic, and in both the `√n` **cancels**: the quantity being bounded is
`4·(d/σ)·√n = 4δ·ln 2/σ` at `d = δ·ln 2/√n`.  The three lemmas below are those two statements
verbatim, proved from the dimension-free hypothesis `δ ≤ σ/12` instead, plus the exact
threshold.

**Nothing here re-proves the big theorem.**  Relaxing its binder means editing
`SpeedyConductanceSharp.lean`, which this file does not own.  It is also *not needed* for the
main result: `metropolis_hfloor_forces_step_cap` puts the operative step at `Θ(σ/√n)`, well
inside the existing cap. -/

/-- **The exact threshold: `hδσ`'s real content is `16·(ln 2)·δ ≤ σ`, with no `n` in it.**
At `d = δ·ln 2/√n` the quantity `4(d/σ)√n` is `4δ·ln 2/σ`, so the `√n` cancels identically. -/
theorem isoStep_quarter_iff {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ) :
    4 * ((δ * Real.log 2 / Real.sqrt n) / σ) * Real.sqrt n ≤ 1 / 4
      ↔ 16 * Real.log 2 * δ ≤ σ := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hrw : 4 * ((δ * Real.log 2 / Real.sqrt n) / σ) * Real.sqrt n
      = 4 * δ * Real.log 2 / σ := by field_simp
  rw [hrw, div_le_iff₀ hσ]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **`SpeedyConductanceSharp.lean:489`'s side condition, from a dimension-free cap.**
Identical statement to `Arlib.MarkovChains.four_mul_isoStep_div_sigma_le_quarter`, with
`δ ≤ σ/(8√n)` weakened to `δ ≤ σ/12`. -/
theorem four_mul_isoStep_div_sigma_le_quarter_of_dimension_free {n : ℕ} (hn : 2 ≤ n)
    {σ δ : ℝ} (hσ : 0 < σ) (hcap : δ ≤ σ / 12) :
    4 * ((δ * Real.log 2 / Real.sqrt n) / σ) * Real.sqrt n ≤ 1 / 4 := by
  rw [isoStep_quarter_iff hn hσ]
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- **`SpeedyConductanceSharp.lean:367`'s side condition, from a dimension-free cap.**
Identical statement to `Arlib.MarkovChains.isoStep_conductance_le_inv_160`, with
`δ ≤ σ/(8√n)` weakened to `δ ≤ σ/12`. -/
theorem isoStep_conductance_le_inv_160_of_dimension_free {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hcap : δ ≤ σ / 12) :
    δ * Real.log 2 / (640 * σ * Real.sqrt n) ≤ 1 / 160 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at this
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **`δ ≤ σ/8` is *not* attainable, even dimension-free.**  At `δ = σ/8` the density branch
sits at `4δ·ln 2/σ = (ln 2)/2 ≈ 0.347 > 1/4`, above `cor:overlap`'s threshold.  So the honest
dimension-free cap is `δ ≤ σ/(16 ln 2) ≈ σ/11.09`, not `σ/8`: the `√n` in `hδσ` is removable,
the constant `8` is not. -/
theorem not_isoStep_quarter_at_sigma_div_eight {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    ¬ (4 * ((σ / 8 * Real.log 2 / Real.sqrt n) / σ) * Real.sqrt n ≤ 1 / 4) := by
  rw [isoStep_quarter_iff hn hσ]
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  intro h
  nlinarith

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.metropolis_hfloor_forces_step_cap
#print axioms Arlib.MarkovChains.acceptance_floor_exp_small_of_large_step
#print axioms Arlib.MarkovChains.acceptance_floor_at_step_sigma_div_eight
#print axioms Arlib.MarkovChains.acceptance_factor_ge_of_step_le
#print axioms Arlib.MarkovChains.speedyGaussian_reparam_conclusion
#print axioms Arlib.MarkovChains.speedyGaussian_reparam_cap
#print axioms Arlib.MarkovChains.speedy_sqrt_gain
#print axioms Arlib.MarkovChains.speedy_old_bound_at_operative_step
#print axioms Arlib.MarkovChains.speedy_new_bound_at_operative_step
#print axioms Arlib.MarkovChains.sup_bounds_agree_at_own_caps
#print axioms Arlib.MarkovChains.isoStep_quarter_iff
#print axioms Arlib.MarkovChains.four_mul_isoStep_div_sigma_le_quarter_of_dimension_free
#print axioms Arlib.MarkovChains.isoStep_conductance_le_inv_160_of_dimension_free
#print axioms Arlib.MarkovChains.not_isoStep_quarter_at_sigma_div_eight
