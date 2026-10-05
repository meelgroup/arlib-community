/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.ConductanceToTV
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.DeltaCap

/-!
# What the `√n` in the conductance is worth in steps

The conductance route for the Metropolis-filtered Gaussian kernel was sharpened by a factor
`√n`: at step `δ` the certified bound went from `Φ ≥ δ·ln 2/(640·σ·n)` to
`Φ ≥ δ·ln 2/(640·σ·√n)`, and `Arlib.MarkovChains.metropolis_hfloor_forces_step_cap`
(`DeltaCap.lean:143`) shows the acceptance floor forces the operative step to `δ = Θ(σ/√n)`.
Evaluated there the two bounds are `ln 2/(5120·n)` and `ln 2/(5120·n^{3/2})`
(`Arlib.MarkovChains.speedy_new_bound_at_operative_step`,
`Arlib.MarkovChains.speedy_old_bound_at_operative_step`).

Since a conductance mixing bound scales as `Φ⁻²`, that is a factor `n` in the step count.
**Up to now that consequence existed only as prose in module docstrings.**  This file makes
it a theorem.

## The conductance bound is a hypothesis here

Nothing in this file proves a conductance bound, and no file that proves one is imported.
Every theorem below takes `ENNReal.ofReal (…) ≤ conductance P pi` as a binder, in exactly
the shape `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge` and
`Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell_comparable` state it.  That is the
`CLAUDE.md` §1 split: the consequence is proved over *any* kernel with the stated
conductance, and the composition with a particular kernel is a separate step.

## What is proved

*The arithmetic (§1).*  `dim_mul_sq_log_two_div_dim_sqrt` — `n·Φ_old² = Φ_new²` at the
operative step, the crux identity; `stepCount_new_eq`, `stepCount_old_eq` — the closed forms
`5120²·n²·C/(ln 2)²` and `5120²·n³·C/(ln 2)²`; `stepCount_old_eq_dim_mul_new` — the ratio,
`C/Φ_old² = n·(C/Φ_new²)`, for every numerator `C`.

*The mixing theorems (§2–§4).*  `mixesWithin_of_conductance_of_stepCount` is the workhorse:
`Arlib.MarkovChains.mixesWithin_of_conductance_of_smallSets` (`ConductanceToTV.lean:336`)
with its abstract `conductanceMixingTime` deadline replaced by the explicit real bound
`(log M + 2·log(1/ε))/Φ² + 1` of `Arlib.MarkovChains.conductanceMixingTime_le`.
`mixesWithin_of_conductance_sqrt` reads it at `Φ = δ·ln 2/(640·σ·√n)`, and
**`mixesWithin_at_operative_step`** — the headline — at `δ = σ/(8√n)`, where `σ` cancels:

    5120²·n²·(log M + 2·log(1/ε))/(ln 2)² + 1     steps suffice          (new route)
    5120²·n³·(log M + 2·log(1/ε))/(ln 2)² + 1     steps suffice          (old route)

the second being `mixesWithin_at_operative_step_old_route`, the same machinery at
`Φ ≥ ln 2/(5120·n^{3/2})`, so that both numbers exist as theorems side by side.
`conductanceMixingTime_at_operative_step_le` and
`conductanceMixingTime_at_operative_step_old_le` are the same two counts as bounds on the
deadline itself.

*The ratio (§5).*  `stepCount_old_eq_dim_mul_new` is an exact equality of the real bounds.
For the deadlines — the natural numbers `conductanceMixingTime` returns — the factor `n` is
bracketed on both sides, the slack being one `⌈·⌉` and nothing else:

* `conductanceMixingTime_old_le_dim_mul_new` — `T_old ≤ n · T_new`;
* `dim_mul_conductanceMixingTime_new_sub_one_le_old` — `n · (T_new − 1) ≤ T_old`.

*Non-vacuity (§6).*  `mixesWithin_at_operative_step_const_piHalf` satisfies every hypothesis
of the headline theorem at once, on `Bool`, and derives its conclusion *through* it.

## Plain chain versus lazy chain, and the one hypothesis that is not discharged

The `-of-stepCount` route consumes `Arlib.MarkovChains.mixesWithin_of_conductance_of_smallSets`,
whose ingredients are the hard direction of Cheeger (`Cheeger.lean:1584`) and the `L²`
contraction (`L2Mixing.lean:976`).  Those need `HasNonnegSpectrum P pi`, and it is **not**
removable: `ConductanceToTV.lean:229–243` records the swap kernel on `Bool`, reversible with
`Φ = 1`, for which the decay bound is false.  So:

* the **plain-chain** theorems (`mixesWithin_at_operative_step` and friends) carry `hpsd :
  HasNonnegSpectrum P pi` as an explicit binder.  Nothing in this repository proves it for
  `metropolisGaussian`; it would take a Metropolis-specific spectral fact, the analogue of
  the hit-and-run gap recorded at `ConductanceToTV.lean:97–104`;
* the **lazy-chain** theorems (`mixesWithin_lazy_at_operative_step` and friends) assume no
  spectral property at all — `Arlib.MarkovChains.hasNonnegSpectrum_lazy` supplies it from
  reversibility of `P` — at exactly four times the deadline, the factor `4` being
  `Arlib.MarkovChains.conductance_lazy`'s exact halving of the conductance.  Their
  conductance hypothesis is still about the **plain** kernel `P`.

The remaining binders are the same in both: `hrev` (reversibility), `hsmall` (some
measurable set has `pi`-mass in `(0, 1/2]`, the kernel-free non-degeneracy hypothesis of
`ConductanceToTV.lean`), `hM`/`hwarm` (an `M`-warm start — a mixing bound from a conductance
is *always* warm-start-relative), and `0 < ε ≤ 1`.

**Nothing here is a statement about the Metropolis kernel, about a convex body, or about
running time.**  It is the `Φ⁻²` arithmetic, made a theorem, over any chain meeting the
stated hypotheses.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## 1. The two conductances, and the arithmetic relating them -/

/-- `0 < ln 2/(5120·n)` — the conductance the `√n` route certifies at the operative step. -/
theorem log_two_div_dim_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log 2 / (5120 * (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- `ln 2/(5120·n) ≤ 1`. -/
theorem log_two_div_dim_le_one {n : ℕ} (hn : 2 ≤ n) : Real.log 2 / (5120 * (n : ℝ)) ≤ 1 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  rw [div_le_one (by linarith)]
  linarith

/-- `0 < ln 2/(5120·n^{3/2})` — the conductance the old `δ/n` route certifies at the same
step.  `n^{3/2}` is written `n·√n` throughout, matching
`Arlib.MarkovChains.speedy_old_bound_at_operative_step`. -/
theorem log_two_div_dim_sqrt_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- `ln 2/(5120·n^{3/2}) ≤ 1`. -/
theorem log_two_div_dim_sqrt_le_one {n : ℕ} (hn : 2 ≤ n) :
    Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n)) ≤ 1 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (n : ℝ) by linarith)
    rwa [Real.sqrt_one] at h
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- **The crux identity: the `√n` gain in the conductance is exactly a factor `n` in `Φ²`.**

`n · (ln 2/(5120·n^{3/2}))² = (ln 2/(5120·n))²`.  Every step-count statement below is this
identity read through `1/Φ²`. -/
theorem dim_mul_sq_log_two_div_dim_sqrt {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) ^ 2
      = (Real.log 2 / (5120 * (n : ℝ))) ^ 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  have hexp : (5120 * ((n : ℝ) * Real.sqrt n)) ^ 2
      = 5120 ^ 2 * (n : ℝ) ^ 2 * (Real.sqrt n * Real.sqrt n) := by ring
  rw [div_pow, div_pow, hexp, hsq]
  field_simp

/-- **The `√n`-route step count, in closed form.**  `C/Φ²` at `Φ = ln 2/(5120·n)` is
`5120²·n²·C/(ln 2)²`. -/
theorem stepCount_new_eq {n : ℕ} (hn : 2 ≤ n) (C : ℝ) :
    C / (Real.log 2 / (5120 * (n : ℝ))) ^ 2 = 5120 ^ 2 * (n : ℝ) ^ 2 * C / Real.log 2 ^ 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_pow]
  field_simp

/-- **The old route's step count, in closed form.**  `C/Φ²` at `Φ = ln 2/(5120·n^{3/2})` is
`5120²·n³·C/(ln 2)²` — a factor `n` more than `stepCount_new_eq`. -/
theorem stepCount_old_eq {n : ℕ} (hn : 2 ≤ n) (C : ℝ) :
    C / (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) ^ 2
      = 5120 ^ 2 * (n : ℝ) ^ 3 * C / Real.log 2 ^ 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : (5120 * ((n : ℝ) * Real.sqrt n)) ^ 2
      = 5120 ^ 2 * (n : ℝ) ^ 2 * (Real.sqrt n * Real.sqrt n) := by ring
  rw [div_pow, hexp, hsq]
  field_simp

/-- **The ratio, as an identity between the two step counts.**  For *every* numerator `C` —
in particular `C = log M + 2 log(1/ε)`, the numerator both mixing bounds below carry — the
old route's `C/Φ_old²` is exactly `n` times the new route's `C/Φ_new²`.

This is the honest form of "a factor `n` off the step count": it is an equality of the
*leading terms*, before the ceiling that turns a real bound into a number of steps.  The
ceiling costs at most `+1`; `conductanceMixingTime_old_le_dim_mul_new` and
`dim_mul_conductanceMixingTime_new_sub_one_le_old` bracket the actual deadlines. -/
theorem stepCount_old_eq_dim_mul_new {n : ℕ} (hn : 2 ≤ n) (C : ℝ) :
    C / (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) ^ 2
      = (n : ℝ) * (C / (Real.log 2 / (5120 * (n : ℝ))) ^ 2) := by
  rw [stepCount_old_eq hn, stepCount_new_eq hn]
  ring

/-- `2·log(√M/ε) = log M + 2·log(1/ε)`, the numerator of `conductanceMixingTime_le` written
as the `mixingTime` of `conductanceMixingTime`'s own definition consumes it. -/
theorem two_mul_log_sqrt_div_eq {M eps : ℝ} (hM : 0 < M) (heps : 0 < eps) :
    2 * Real.log (Real.sqrt M / eps) = Real.log M + 2 * Real.log (1 / eps) := by
  rw [Real.log_div (Real.sqrt_ne_zero'.2 hM) heps.ne', Real.log_sqrt hM.le, one_div,
    Real.log_inv]
  ring

/-! ## 2. From a conductance bound to an explicit number of steps -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The workhorse: a conductance bound, an explicit step count.**

Every theorem below is this one at a particular `phi`.  It is
`Arlib.MarkovChains.mixesWithin_of_conductance_of_smallSets` (`ConductanceToTV.lean:336`)
with its `conductanceMixingTime` deadline replaced by the explicit real bound of
`Arlib.MarkovChains.conductanceMixingTime_le`, and with the conductance hypothesis in the
`ℝ≥0∞` form a conductance theorem states it in. -/
theorem mixesWithin_of_conductance_of_stepCount {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi) (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M phi eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (hphi0 : 0 < phi) (hphi1 : phi ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (hcond : ENNReal.ofReal phi ≤ conductance P pi)
    {t : ℕ} (ht : (Real.log M + 2 * Real.log (1 / eps)) / phi ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin P pi mu0 t (ENNReal.ofReal eps) := by
  have hsqrtM : (1 : ℝ) ≤ Real.sqrt M := by
    have h := Real.sqrt_le_sqrt hM
    rwa [Real.sqrt_one] at h
  have hle : eps ≤ Real.sqrt M := le_trans heps1 hsqrtM
  have hctop : conductance P pi ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (conductance_le_one P pi hsmall)
  have hphi : phi ≤ (conductance P pi).toReal := by
    have h := ENNReal.toReal_mono hctop hcond
    rwa [ENNReal.toReal_ofReal hphi0.le] at h
  have hT : conductanceMixingTime M phi eps ≤ t := by
    have hcast : ((conductanceMixingTime M phi eps : ℕ) : ℝ) ≤ (t : ℝ) :=
      le_trans (conductanceMixingTime_le hM hphi0 heps0 hle) ht
    exact_mod_cast hcast
  exact mixesWithin_of_conductance_of_smallSets hrev hpsd hsmall hM hwarm hphi0 hphi1 heps0
    hphi hT

/-- **The same for the lazy chain, at four times the deadline and no spectral hypothesis.**

`Arlib.MarkovChains.hasNonnegSpectrum_lazy` supplies `hpsd` from reversibility of `P` alone,
and `Arlib.MarkovChains.conductance_lazy` charges exactly a factor `2` in the conductance —
hence the `4` in front of the step count, which is `(phi/2)⁻² = 4·phi⁻²`.  The conductance
hypothesis is still about the **plain** kernel `P`. -/
theorem mixesWithin_lazy_of_conductance_of_stepCount {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M phi eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (hphi0 : 0 < phi) (hphi1 : phi ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (hcond : ENNReal.ofReal phi ≤ conductance P pi)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) / phi ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy P) pi mu0 t (ENNReal.ofReal eps) := by
  refine mixesWithin_of_conductance_of_stepCount (isReversible_lazy hrev)
    (hasNonnegSpectrum_lazy hrev) hsmall hM hwarm (by linarith) (by linarith) heps0 heps1
    (ofReal_half_le_conductance_lazy hcond) ?_
  have hrw : (Real.log M + 2 * Real.log (1 / eps)) / (phi / 2) ^ 2
      = 4 * ((Real.log M + 2 * Real.log (1 / eps)) / phi ^ 2) := by
    rw [div_pow]
    field_simp
    ring
  rw [hrw]
  exact ht

/-! ## 3. The `√n` conductance bound, at a general step `δ`

The conductance bound is a **hypothesis** here, in exactly the shape
`Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge` and
`Arlib.MarkovChains.conductance_speedyGaussian_ge_of_ell_comparable` produce it.  Nothing in
this file proves a conductance bound, and nothing here imports a file that does: composing
the two is the caller's job. -/

/-- **`Φ ≥ δ·ln 2/(640·σ·√n)` gives an explicit mixing time.**

`hδσ` is the step cap that the conductance theorems already carry (`hδσ` there too), and it
is what makes `phi ≤ 1` (`Arlib.MarkovChains.isoStep_conductance_le_inv_160`, which gives the
much better `phi ≤ 1/160`). -/
theorem mixesWithin_of_conductance_sqrt {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi) (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hΦ : ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ≤ conductance P pi)
    {t : ℕ} (ht : (Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin P pi mu0 t (ENNReal.ofReal eps) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hphi0 : 0 < δ * Real.log 2 / (640 * σ * Real.sqrt n) := by positivity
  have hphi1 : δ * Real.log 2 / (640 * σ * Real.sqrt n) ≤ 1 :=
    le_trans (isoStep_conductance_le_inv_160 hn hσ hδ hδσ) (by norm_num)
  exact mixesWithin_of_conductance_of_stepCount hrev hpsd hsmall hM hwarm hphi0 hphi1 heps0
    heps1 hΦ ht

/-- **The lazy counterpart of `mixesWithin_of_conductance_sqrt`**, with no spectral
hypothesis and four times the deadline. -/
theorem mixesWithin_lazy_of_conductance_sqrt {n : ℕ} (hn : 2 ≤ n) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (hδσ : δ ≤ σ / (8 * Real.sqrt n)) {P : Kernel Ω Ω} [IsMarkovKernel P]
    {pi : Measure Ω} [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hΦ : ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ≤ conductance P pi)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps))
      / (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy P) pi mu0 t (ENNReal.ofReal eps) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hphi0 : 0 < δ * Real.log 2 / (640 * σ * Real.sqrt n) := by positivity
  have hphi1 : δ * Real.log 2 / (640 * σ * Real.sqrt n) ≤ 1 :=
    le_trans (isoStep_conductance_le_inv_160 hn hσ hδ hδσ) (by norm_num)
  exact mixesWithin_lazy_of_conductance_of_stepCount hrev hsmall hM hwarm hphi0 hphi1 heps0
    heps1 hΦ ht

/-! ## 4. At the operative step `δ = σ/(8√n)`

`Arlib.MarkovChains.metropolis_hfloor_forces_step_cap` (`DeltaCap.lean:143`) shows the
Metropolis acceptance floor forces `δ = Θ(σ/√n)`.  Evaluated there the two conductance
bounds are

    (new)  Φ ≥ ln 2/(5120·n)          `Arlib.MarkovChains.speedy_new_bound_at_operative_step`
    (old)  Φ ≥ ln 2/(5120·n^{3/2})    `Arlib.MarkovChains.speedy_old_bound_at_operative_step`

— `σ` cancels in both.  The step counts below are those two numbers read through
`conductanceMixingTime_le`. -/

/-- **The `√n` route's step count at the operative step.**
`(log M + 2 log(1/ε))/Φ² + 1` at `Φ = ln 2/(5120·n)` is `5120²·n²·(log M + 2 log(1/ε))/(ln 2)²
+ 1`: **quadratic** in the dimension. -/
theorem conductanceMixingTime_at_operative_step_le {n : ℕ} (hn : 2 ≤ n) {M eps : ℝ}
    (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    (conductanceMixingTime M (Real.log 2 / (5120 * (n : ℝ))) eps : ℝ)
      ≤ 5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 := by
  have hsqrtM : (1 : ℝ) ≤ Real.sqrt M := by
    have h := Real.sqrt_le_sqrt hM
    rwa [Real.sqrt_one] at h
  have h := conductanceMixingTime_le hM (log_two_div_dim_pos hn) heps0 (le_trans heps1 hsqrtM)
  rwa [stepCount_new_eq hn] at h

/-- **The old route's step count at the same step.**  `Φ = ln 2/(5120·n^{3/2})` gives
`5120²·n³·(log M + 2 log(1/ε))/(ln 2)² + 1`: **cubic** in the dimension. -/
theorem conductanceMixingTime_at_operative_step_old_le {n : ℕ} (hn : 2 ≤ n) {M eps : ℝ}
    (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    (conductanceMixingTime M (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) eps : ℝ)
      ≤ 5120 ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 := by
  have hsqrtM : (1 : ℝ) ≤ Real.sqrt M := by
    have h := Real.sqrt_le_sqrt hM
    rwa [Real.sqrt_one] at h
  have h :=
    conductanceMixingTime_le hM (log_two_div_dim_sqrt_pos hn) heps0 (le_trans heps1 hsqrtM)
  rwa [stepCount_old_eq hn] at h

/-- **The headline: `O(n²)` steps from the `√n` conductance bound.**

At the operative step `δ = σ/(8√n)` the certified conductance is `ln 2/(5120·n)` — `σ` has
cancelled — and

    5120²·n²·(log M + 2·log(1/ε))/(ln 2)² + 1

steps suffice for total variation `ε` from an `M`-warm start.  The hypothesis `hΦ` is written
at the operative step *before* the cancellation, so it is literally what a conductance
theorem of the form `Φ ≥ δ·ln 2/(640·σ·√n)` delivers when handed `δ = σ/(8√n)`. -/
theorem mixesWithin_at_operative_step {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ)
    {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω} [IsProbabilityMeasure pi]
    (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hΦ : ENNReal.ofReal (σ / (8 * Real.sqrt n) * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance P pi)
    {t : ℕ} (ht : 5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin P pi mu0 t (ENNReal.ofReal eps) := by
  rw [speedy_new_bound_at_operative_step hn hσ] at hΦ
  refine mixesWithin_of_conductance_of_stepCount hrev hpsd hsmall hM hwarm
    (log_two_div_dim_pos hn) (log_two_div_dim_le_one hn) heps0 heps1 hΦ ?_
  rwa [stepCount_new_eq hn]

/-- **The old route at the operative step: `O(n³)` steps.**

Same machinery, same step, same `σ`; the only change is the conductance bound
`Φ ≥ δ·ln 2/(640·σ·n)` of the `δ/n` overlap route.  The step count is
`5120²·n³·(log M + 2·log(1/ε))/(ln 2)² + 1`. -/
theorem mixesWithin_at_operative_step_old_route {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ)
    {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω} [IsProbabilityMeasure pi]
    (hrev : IsReversible P pi) (hpsd : HasNonnegSpectrum P pi)
    (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hΦ : ENNReal.ofReal (σ / (8 * Real.sqrt n) * Real.log 2 / (640 * σ * (n : ℝ)))
      ≤ conductance P pi)
    {t : ℕ} (ht : 5120 ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin P pi mu0 t (ENNReal.ofReal eps) := by
  rw [speedy_old_bound_at_operative_step hn hσ] at hΦ
  refine mixesWithin_of_conductance_of_stepCount hrev hpsd hsmall hM hwarm
    (log_two_div_dim_sqrt_pos hn) (log_two_div_dim_sqrt_le_one hn) heps0 heps1 hΦ ?_
  rwa [stepCount_old_eq hn]

/-- **The headline for the lazy chain**, where `hpsd` is not assumed: `4·5120²·n²·(log M +
2·log(1/ε))/(ln 2)² + 1` steps.  The factor `4` is `Arlib.MarkovChains.conductance_lazy`. -/
theorem mixesWithin_lazy_at_operative_step {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ)
    {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω} [IsProbabilityMeasure pi]
    (hrev : IsReversible P pi) (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hΦ : ENNReal.ofReal (σ / (8 * Real.sqrt n) * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance P pi)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy P) pi mu0 t (ENNReal.ofReal eps) := by
  rw [speedy_new_bound_at_operative_step hn hσ] at hΦ
  refine mixesWithin_lazy_of_conductance_of_stepCount hrev hsmall hM hwarm
    (log_two_div_dim_pos hn) (log_two_div_dim_le_one hn) heps0 heps1 hΦ ?_
  rwa [stepCount_new_eq hn]

/-- **The old route for the lazy chain**: `4·5120²·n³·(log M + 2·log(1/ε))/(ln 2)² + 1`. -/
theorem mixesWithin_lazy_at_operative_step_old_route {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ)
    {P : Kernel Ω Ω} [IsMarkovKernel P] {pi : Measure Ω} [IsProbabilityMeasure pi]
    (hrev : IsReversible P pi) (hsmall : (SmallSets pi (1 / 2)).Nonempty)
    {mu0 : Measure Ω} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 pi) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hΦ : ENNReal.ofReal (σ / (8 * Real.sqrt n) * Real.log 2 / (640 * σ * (n : ℝ)))
      ≤ conductance P pi)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy P) pi mu0 t (ENNReal.ofReal eps) := by
  rw [speedy_old_bound_at_operative_step hn hσ] at hΦ
  refine mixesWithin_lazy_of_conductance_of_stepCount hrev hsmall hM hwarm
    (log_two_div_dim_sqrt_pos hn) (log_two_div_dim_sqrt_le_one hn) heps0 heps1 hΦ ?_
  rwa [stepCount_old_eq hn]

/-! ## 5. The ratio: a factor `n` in the step count, machine-checked

`stepCount_old_eq_dim_mul_new` is the exact statement at the level of the real bound.  The
two theorems below say the same thing about the **deadlines themselves** — the natural
numbers `conductanceMixingTime` returns — and bracket the factor `n` from both sides.  The
slack in each is one application of `⌈·⌉`, nothing else. -/

/-- **Upper bracket: the old route's deadline is at most `n` times the new one.**

No positivity hypothesis on `M` or `ε` is needed: at a degenerate `(M, ε)` both ceilings are
`0`. -/
theorem conductanceMixingTime_old_le_dim_mul_new {n : ℕ} (hn : 2 ≤ n) (M eps : ℝ) :
    conductanceMixingTime M (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) eps
      ≤ n * conductanceMixingTime M (Real.log 2 / (5120 * (n : ℝ))) eps := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hb : (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) ^ 2 ≠ 0 :=
    ne_of_gt (pow_pos (log_two_div_dim_sqrt_pos hn) 2)
  have hkey : Real.log (Real.sqrt M / eps)
        / ((Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) ^ 2 / 2)
      = (n : ℝ) * (Real.log (Real.sqrt M / eps)
        / ((Real.log 2 / (5120 * (n : ℝ))) ^ 2 / 2)) := by
    rw [← dim_mul_sq_log_two_div_dim_sqrt hn]
    field_simp
  unfold conductanceMixingTime mixingTime
  rw [hkey]
  refine Nat.ceil_le.mpr ?_
  push_cast
  exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) hnpos.le

/-- **Lower bracket: the old route's deadline is at least `n` times the new one, less `n`.**

`(n : ℝ) · (T_new − 1) ≤ T_old`.  The `−1` is the ceiling in `T_new` and nothing else: the
pre-ceiling bounds satisfy the exact identity `stepCount_old_eq_dim_mul_new`.  Together with
`conductanceMixingTime_old_le_dim_mul_new` this is the machine-checked form of "the `√n` in
the conductance is a factor `n` in the step count". -/
theorem dim_mul_conductanceMixingTime_new_sub_one_le_old {n : ℕ} (hn : 2 ≤ n) {M eps : ℝ}
    (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    (n : ℝ) * ((conductanceMixingTime M (Real.log 2 / (5120 * (n : ℝ))) eps : ℝ) - 1)
      ≤ (conductanceMixingTime M (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) eps : ℝ) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hsqrtM : (1 : ℝ) ≤ Real.sqrt M := by
    have h := Real.sqrt_le_sqrt hM
    rwa [Real.sqrt_one] at h
  have hle : eps ≤ Real.sqrt M := le_trans heps1 hsqrtM
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnew := conductanceMixingTime_le hM (log_two_div_dim_pos hn) heps0 hle
  have hold : (Real.log M + 2 * Real.log (1 / eps))
        / (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) ^ 2
      ≤ (conductanceMixingTime M (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) eps : ℝ) := by
    have hrw : (Real.log M + 2 * Real.log (1 / eps))
          / (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) ^ 2
        = Real.log (Real.sqrt M / eps)
          / ((Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) ^ 2 / 2) := by
      rw [div_div_eq_mul_div, ← two_mul_log_sqrt_div_eq hM0 heps0]
      ring
    rw [hrw]
    unfold conductanceMixingTime mixingTime
    exact Nat.le_ceil _
  calc (n : ℝ) * ((conductanceMixingTime M (Real.log 2 / (5120 * (n : ℝ))) eps : ℝ) - 1)
      ≤ (n : ℝ) * ((Real.log M + 2 * Real.log (1 / eps))
          / (Real.log 2 / (5120 * (n : ℝ))) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hnn
        linarith
    _ = (Real.log M + 2 * Real.log (1 / eps))
          / (Real.log 2 / (5120 * ((n : ℝ) * Real.sqrt n))) ^ 2 :=
        (stepCount_old_eq_dim_mul_new hn _).symm
    _ ≤ _ := hold

/-! ## 6. Non-vacuity (`CLAUDE.md` §11)

`mixesWithin_at_operative_step` quantifies over a bundle — reversibility, non-negative
spectrum, a small set, an `M`-warm start, and a conductance bound at the operative step.  A
green build over an unsatisfiable bundle certifies nothing, so here is a chain that satisfies
all of it at once, at `n = 2`, `σ = 1`, `M = 2`, `ε = 1/2`, with the conclusion derived
*through* the headline theorem. -/

/-- **Non-vacuity witness for `mixesWithin_at_operative_step`.**

The uniform resampler on `Bool` is `piHalf`-reversible (`isReversible_const`), has
non-negative spectrum (`hasNonnegSpectrum_const`), lives on a space with a set of mass `1/2`
(`singleton_mem_smallSets`), has conductance `1/2 ≥ ln 2/10240` (`conductance_const_piHalf`),
and `dirac true` is `2`-warm for it.  Every hypothesis of the headline theorem is therefore
simultaneously satisfiable, with a non-trivial conclusion (`ε = 1/2 < 1`). -/
theorem mixesWithin_at_operative_step_const_piHalf (t : ℕ)
    (ht : 5120 ^ 2 * (((2 : ℕ)) : ℝ) ^ 2 * (Real.log 2 + 2 * Real.log (1 / (1 / 2)))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin (Kernel.const Bool piHalf) piHalf (Measure.dirac true) t
      (ENNReal.ofReal (1 / 2)) := by
  have hofReal2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  refine mixesWithin_at_operative_step (n := 2) (σ := 1) (M := 2) (by norm_num) one_pos
    (isReversible_const piHalf) (hasNonnegSpectrum_const piHalf)
    ⟨{true}, singleton_mem_smallSets true⟩ (by norm_num) ?_ (by norm_num) (by norm_num) ?_ ht
  · -- `dirac true` is `2`-warm with respect to `piHalf`.
    intro A hA
    rw [hofReal2]
    by_cases h : true ∈ A
    · have h1 : (1 : ℝ≥0∞) / 2 ≤ piHalf A := by
        rw [← piHalf_singleton true]
        exact measure_mono (Set.singleton_subset_iff.2 h)
      calc Measure.dirac true A ≤ 1 := prob_le_one
        _ = 2 * (1 / 2) := by
            rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        _ ≤ 2 * piHalf A := by gcongr
    · simp [Measure.dirac_apply' _ hA, h]
  · -- the conductance at the operative step: `ln 2/10240 ≤ 1/2 = Φ`.
    rw [speedy_new_bound_at_operative_step (n := 2) (by norm_num) one_pos,
      conductance_const_piHalf, ← ofReal_one_half]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlog : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have h2 : (5120 : ℝ) * (((2 : ℕ)) : ℝ) = 10240 := by norm_num
    rw [h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 10240)]
    linarith

/-! ### Axiom audit (`CLAUDE.md` §4) -/

section AxiomCheck

#print axioms log_two_div_dim_pos
#print axioms log_two_div_dim_le_one
#print axioms log_two_div_dim_sqrt_pos
#print axioms log_two_div_dim_sqrt_le_one
#print axioms dim_mul_sq_log_two_div_dim_sqrt
#print axioms stepCount_new_eq
#print axioms stepCount_old_eq
#print axioms stepCount_old_eq_dim_mul_new
#print axioms two_mul_log_sqrt_div_eq
#print axioms mixesWithin_of_conductance_of_stepCount
#print axioms mixesWithin_lazy_of_conductance_of_stepCount
#print axioms mixesWithin_of_conductance_sqrt
#print axioms mixesWithin_lazy_of_conductance_sqrt
#print axioms conductanceMixingTime_at_operative_step_le
#print axioms conductanceMixingTime_at_operative_step_old_le
#print axioms mixesWithin_at_operative_step
#print axioms mixesWithin_at_operative_step_old_route
#print axioms mixesWithin_lazy_at_operative_step
#print axioms mixesWithin_lazy_at_operative_step_old_route
#print axioms conductanceMixingTime_old_le_dim_mul_new
#print axioms dim_mul_conductanceMixingTime_new_sub_one_le_old
#print axioms mixesWithin_at_operative_step_const_piHalf

end AxiomCheck

end Arlib.MarkovChains
