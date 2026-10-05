/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.EllLogConcave

/-!
# `thm:iso` for a **weighted** density `1_K·f·e^{−‖x‖²/(2σ²)}`, `S₁ S₂ S₃` merely measurable

`Arlib.gaussianIndicator_isoperimetry_measurable_logTwo` (`Arlib/Convexity/OneDimSharp.lean:676`)
removes both topological restrictions of the open/closed capstone — `S₁, S₂` open, `S₃` closed,
`h` continuous — but only at the **indicator** density `1_K·e^{−‖x‖²/(2σ²)}`.  Its method,
however, is not obviously indicator-specific: it does the partition step **first**, replacing
`S₁, S₂` by `S₁ ∩ K, S₂ ∩ K` (which changes no integral, `h` vanishing off `K`), and then uses
that *on* `K` the density is continuous and strictly positive, so the density branch of `hsep` is
no longer free and the **metric** branch holds for every pair; the continuity step is then run
with the metric branch supplied unconditionally and `densDist h_j` never appears.

This file tests that method at `h = 1_K·f·e^{−‖x‖²/(2σ²)}` and reports the exact hypothesis
bundle on `f` that it needs.

## The answer: it generalises, but **not** on continuity and positivity alone

The `(A)` half — dominated convergence along `h_j = e^{−j·dist(x,K̄)}·f·e^{−‖x‖²/(2σ²)}` — costs
nothing new beyond integrability of `f·e^{−‖x‖²/(2σ²)}`.  The `(B)` half does.  What the crux
needs on `K` is not "the density branch is not free" but the **quantitative** statement

    d_h(u,v) ≤ M·‖u − v‖   for `u, v ∈ K`,

because the thresholds in the statement — `d / log 2` on the metric side, `4(d/σ)√n` on the
density side — are *fixed numbers*.  Continuity of `f` on a compact `K` gives a modulus
`ω` with `d_h(u,v) ≥ c ⟹ ‖u − v‖ ≥ ρ(c) > 0`, but `ρ(c)` is not a linear function of `c` and
nothing ties it to `d`.  Concretely: for `K = closedBall 0 1` the family
`f_M(x) = e^{−M·⟪e,x⟫}` is log-concave, continuous and strictly positive for every `M`, and for a
pair `u, v ∈ K` with `‖u‖ = ‖v‖` (so the Gaussian factor cancels) and `⟪e, u−v⟫ = ‖u − v‖ = t`
one gets `d_h(u,v) = 1 − e^{−M·t}`, which reaches the fixed threshold `4(d/σ)√n` already at
`t = Θ(1/M) → 0`.  So for fixed `d, σ, R, n` the density branch can be satisfied by pairs
arbitrarily close together, the cores `S₁ ∩ K`, `S₂ ∩ K` may touch, and the disjoint open
enlargement the reduction runs on does not exist — which is exactly the obstruction
`Arlib.exists_separated_no_disjoint_open_enlargement` (`IsoOpenClosed.lean:1205`) exhibits,
merely relocated from `{h = 0}` to the interior of `K`.

This is a statement about **this method**, not about the truth of the conclusion: the open/closed
capstone `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` itself carries no Lipschitz
hypothesis, and nothing here shows the measurable statement is false for a merely continuous `f`.

So the bundle that works adds one quantitative binder and one compatibility binder:

* `hf0 : ∀ x, 0 ≤ f x`, `hflc : IsLogConcave f`, `hfc : Continuous f`, `hfB : ∀ x, f x ≤ B` —
  what the open/closed capstone asks of the approximants `h_j`, whose log-concave factor is
  `e^{−j·dist(x,K̄)}·f`.  Continuity is needed **globally**: `e^{−j·dist(x,K̄)}` is strictly
  positive off `K` too, so it cannot mask a discontinuity of `f` there.
* `hfKpos : ∀ x ∈ K, 0 < f x` — strict positivity on `K`, as anticipated.
* `hfLip : ∀ u ∈ K, ∀ v ∈ K, f u ≤ f v·e^{Lf·‖u−v‖}` with `hLf : 0 ≤ Lf` — **the new binder**:
  `f` is log-Lipschitz on `K` with an explicit constant.
* `hLσ : √3·(σ²·Lf + R) ≤ 2σ√n` — the compatibility, replacing the indicator theorem's
  `hRσ : √3·R ≤ 2σ√n`, which it becomes **verbatim** at `Lf = 0`.  The generalisation is
  therefore conservative: it specialises back to the indicator hypothesis exactly.

## Main results

* `Arlib.densDist_le_of_exp_bound` — a two-sided multiplicative bound caps `densDist`:
  `d_h(u,v) ≤ 1 − e^{−s} ≤ s`.  The only property of the density the `(B)` step uses.
* `Arlib.gaussianWeightReal_le_mul_exp` — the Gaussian weight is log-Lipschitz with constant
  `R/σ²` on `{‖·‖ ≤ R}`.
* `Arlib.norm_sub_ge_of_densDist_weighted` — **the crux.**  On `K`,
  `4(d/σ)√n ≤ d_h(u,v)` forces `‖u − v‖ ≥ 4σd√n/(σ²Lf + R) ≥ 2√3·d`.
* `Arlib.exists_disjoint_open_enlargement_weighted` — **(B), landed.**
* `Arlib.tendsto_setIntegral_expNegInfDist_mul_weighted` — **(A), landed**, dominated by
  `f·e^{−‖x‖²/(2σ²)}`.
* `Arlib.weightedIndicator_isoperimetry_measurable_logTwo` — **the deliverable.**
* `Arlib.ellGaussian_isoperimetry_measurable_logTwo` — the instantiation at `f := ℓ`, the local
  conductance, using `Arlib.isLogConcave_ell_toReal` and `Arlib.continuous_ell_toReal`
  (`Arlib/Convexity/EllLogConcave.lean`).  This is the measurable-partition isoperimetry for
  `1_K·ℓ·e^{−‖x‖²/(2σ²)}`; `EllLogConcave.lean` had it only for `S₁, S₂` open and `S₃` closed.
* `Arlib.weightedIndicator_isoperimetry_measurable_logTwo_strict_witness`,
  `Arlib.ellGaussian_isoperimetry_measurable_logTwo_strict_witness` — non-vacuity, **strict**:
  each exhibits an admissible partition at which the left-hand side of the conclusion is
  *strictly positive*, so the theorem is not the trivial `0 ≤ something`.  The first runs at a
  genuinely non-constant `f(x) = e^{−‖x‖/2}` (`Lf = 1/2`), so it is not the indicator theorem in
  disguise; the second runs at `K = closedBall 0 (1/2)`, `δ = 4`, where `K` lies inside every
  proposal ball centred in it, so `ℓ` is *constant* on `K` and `hellLip` holds with `Lf = 0`.

## Is a kernel reversible for `1_K·ℓ·e^{−‖x‖²/(2σ²)}` buildable?  Yes — assessment only

`Arlib/MarkovChains/Continuous/EllFloor.lean` records that nothing in this repository is
reversible for that density: `metropolisGaussian` is reversible for `1_K·γ`
(`MetropolisGaussian.lean:586`) and `speedyWalk` for `1_K·ℓ`
(`SpeedyWalk.lean:379, 403`).  Reading the two definitions and the two reversibility proofs, the
missing kernel is the obvious hybrid, and the `ℓ` cancels for a structural reason.

*The two existing move densities.*  `speedyWalk K δ` (`SpeedyWalk.lean:186`) moves with density
`q_s(x,y) = (vol(B(x,δ)∩K))⁻¹·1_{B(x,δ)∩K}(y)`, i.e. `(ℓ(x)·vol(δBₙ))⁻¹·1_{B(x,δ)∩K}(y)`, plus a
holding atom on the `StuckPoints`; detailed balance for `ellMeasure = 1_K·ℓ·dx` is the pointwise
identity `ℓ(x)·q_s(x,y) = vol(δBₙ)⁻¹·1_{B(x,δ)}(y)·1_K(y)` (`ell_mul_speedyWalk`), whose
right-hand side is symmetric on `K × K`.  `metropolisGaussian K δ s`
(`MetropolisGaussian.lean:444`) moves with density
`q_m(x,y) = vol(δBₙ)⁻¹·1_K(y)·1_{B(x,δ)}(y)·min(1, g(y)/g(x))`, and detailed balance for `1_K·g`
is `g(x)·q_m(x,y) = vol(δBₙ)⁻¹·1_K(y)·1_{B(x,δ)}(y)·min(g x, g y)`
(`gaussianWeight_mul_metropolisDensity_comm`, `MetropolisGaussian.lean:365`).

*The hybrid.*  A "speedy Metropolis–Gaussian" kernel would propose `y` uniformly from
`B(x,δ) ∩ K` — the **speedy** proposal, not the plain ball — and then apply the Gaussian
Metropolis filter `min(1, g(y)/g(x))`, staying put otherwise:

    q(x,y) = (ℓ(x)·vol(δBₙ))⁻¹·1_{B(x,δ)∩K}(y)·min(1, g(y)/g(x)).

Against the target density `π(x) = 1_K(x)·ℓ(x)·g(x)` this gives

    π(x)·q(x,y) = vol(δBₙ)⁻¹·1_K(x)·1_K(y)·1_{B(x,δ)}(y)·min(g x, g y),

which is symmetric in `(x,y)`: the `1/ℓ(x)` normalisation of the speedy proposal cancels the
`ℓ(x)` of the target exactly — the same cancellation `ell_mul_speedyWalk` performs — and the
filter symmetrises `g` exactly as `gaussianWeight_mul_metropolisDensity_comm` does.  So the
kernel exists and detailed balance holds.

*What proving it would take.*  No new mathematics; a merge of the two existing proofs.  (i) A
`def` of the kernel with its `measurable'` field, mirroring `speedyWalkAux`'s: the `ℓ`-normaliser
is `measurable_volume_inter_ball`, the numerator is
`measurable_setLIntegral_metropolisDensity` restricted to `K`.  (ii) A `StuckPoints`-style guard
and holding atom, plus a **new** `≤ 1` lemma for the move mass — it is now
`ℓ(x)·(mean acceptance on B(x,δ)∩K)`, so neither `metropolisMove_le_one` nor the speedy walk's
own Markov proof applies verbatim.  (iii) The pointwise crux above, which needs the same
`vol(B(x,δ)∩K) = 0` case split as `ell_mul_speedyWalk` and the same `ell_mul_stuck_indicator`
to kill the holding term.  (iv) A `flow` lemma and Tonelli
(`lintegral_lintegral_swap`), as in `lintegral_gaussianWeight_mul_metropolisDensity_comm`.
Order of 300–500 lines.  **This file does not build it** — it would need a `def`, which is out of
scope here.

*And it would not by itself close the speedy route.*  `Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex`
(`StarPolar.lean:626`) is stated for `speedyWalk`, not for a hybrid, so a new kernel needs its own
conductance argument; the isoperimetric inequality proved here is one input to such an argument,
not the argument.

## Scope

Isoperimetry only.  Nothing here is a conductance bound, a mixing bound, a spectral-gap bound or
a runtime statement, and none of it may be quoted as one.  There is no `def`, `structure`, `class`
or `axiom` in this file; every declaration is a `theorem`.
-/

open MeasureTheory Set Filter Metric

open Arlib.MarkovChains

open scoped ENNReal Topology

namespace Arlib

/-! ### `densDist` from a two-sided multiplicative bound -/

section DensDistBound

variable {E : Type*}

/-- **A two-sided multiplicative bound caps `densDist`**, in the ordered case `h v ≤ h u`. -/
theorem densDist_le_of_exp_bound_of_le {h : E → ℝ} {u v : E} {s : ℝ}
    (hu : 0 < h u) (hle : h v ≤ h u) (huv : h u ≤ h v * Real.exp s) :
    densDist h u v ≤ s := by
  have hexpm : Real.exp s * Real.exp (-s) = 1 := by
    rw [← Real.exp_add]; simp
  have hexp : h u * Real.exp (-s) ≤ h v := by
    have h2 := mul_le_mul_of_nonneg_right huv (Real.exp_pos (-s)).le
    rwa [mul_assoc, hexpm, mul_one] at h2
  rw [densDist, max_eq_left hle, abs_of_nonneg (by linarith), div_le_iff₀ hu]
  nlinarith [one_sub_exp_neg_le s, Real.exp_pos (-s)]

/-- **A two-sided multiplicative bound caps `densDist`.**

If `h u ≤ h v·e^s` and `h v ≤ h u·e^s` with both values positive, then
`d_h(u,v) = 1 − min/max ≤ 1 − e^{−s} ≤ s`.  This is the only property of the density that the
`(B)` step of `Arlib.gaussianIndicator_isoperimetry_measurable` uses, and it is what makes the
argument generalise away from indicators. -/
theorem densDist_le_of_exp_bound {h : E → ℝ} {u v : E} {s : ℝ}
    (hu : 0 < h u) (hv : 0 < h v)
    (huv : h u ≤ h v * Real.exp s) (hvu : h v ≤ h u * Real.exp s) :
    densDist h u v ≤ s := by
  rcases le_total (h v) (h u) with hle | hle
  · exact densDist_le_of_exp_bound_of_le hu hle huv
  · rw [densDist_comm]
    exact densDist_le_of_exp_bound_of_le hv hle hvu

end DensDistBound

/-! ### The Gaussian weight is log-Lipschitz on a bounded set -/

section GaussianLip

variable {n : ℕ}

/-- **The Gaussian weight is log-Lipschitz with constant `R/σ²` on the ball of radius `R`.**

`e^{−‖u‖²/(2σ²)} ≤ e^{−‖v‖²/(2σ²)}·e^{(R/σ²)‖u−v‖}`, because
`‖v‖² − ‖u‖² = (‖v‖−‖u‖)(‖v‖+‖u‖) ≤ ‖u−v‖·2R`.  This is the estimate the indicator crux
`Arlib.norm_sub_ge_of_densDist_gaussianIndicator` performs inline; here it is isolated so that a
second log-Lipschitz factor can be multiplied onto it. -/
theorem gaussianWeightReal_le_mul_exp {σ R : ℝ} (hσ : 0 < σ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    gaussianWeightReal (σ ^ 2) u
      ≤ gaussianWeightReal (σ ^ 2) v * Real.exp (R / σ ^ 2 * ‖u - v‖) := by
  have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity
  have hR0 : 0 ≤ R := le_trans (norm_nonneg u) hu
  have hd : ‖v‖ - ‖u‖ ≤ ‖u - v‖ :=
    le_trans (by linarith [neg_abs_le (‖u‖ - ‖v‖)]) (abs_norm_sub_norm_le u v)
  have hkey : ‖v‖ ^ 2 - ‖u‖ ^ 2 ≤ 2 * R * ‖u - v‖ := by
    nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u - v)]
  rw [gaussianWeightReal, gaussianWeightReal, ← Real.exp_add, Real.exp_le_exp]
  have hgoal : (-‖v‖ ^ 2 / (2 * σ ^ 2) + R / σ ^ 2 * ‖u - v‖) - (-‖u‖ ^ 2 / (2 * σ ^ 2))
      = (‖u‖ ^ 2 - ‖v‖ ^ 2 + 2 * R * ‖u - v‖) / (2 * σ ^ 2) := by
    field_simp
    ring
  have h1 : 0 ≤ (‖u‖ ^ 2 - ‖v‖ ^ 2 + 2 * R * ‖u - v‖) / (2 * σ ^ 2) :=
    div_nonneg (by linarith) (by positivity)
  linarith

end GaussianLip

/-! ### (B), the crux: on `K` the density branch has metric content -/

section Separation

variable {n : ℕ}

/-- **(B), the crux, for the weighted density.**

Let `h = 1_K·f·e^{−‖x‖²/(2σ²)}` with `f` strictly positive and **log-Lipschitz with constant
`Lf`** on `K`, and let `‖·‖ ≤ R` on `K`.  Then on `K`

    d_h(u,v) ≤ (Lf + R/σ²)·‖u − v‖,

so the density branch `4(d/σ)√n ≤ d_h(u,v)` forces `‖u − v‖ ≥ 4σd√n/(σ²Lf + R)`, which is at
least `2√3·d` exactly when `√3·(σ²Lf + R) ≤ 2σ√n`.  At `Lf = 0` — `f` constant on `K` — the
hypothesis is `√3·R ≤ 2σ√n`, verbatim the indicator one.

`R > 0` is not assumed: `u ≠ v` forces `0 < ‖u − v‖ ≤ 2R`. -/
theorem norm_sub_ge_of_densDist_weighted {σ d R Lf : ℝ} (hσ : 0 < σ) (hd : 0 < d) (hLf : 0 ≤ Lf)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfKpos : ∀ x ∈ K, 0 < f x)
    (hfLip : ∀ u ∈ K, ∀ v ∈ K, f u ≤ f v * Real.exp (Lf * ‖u - v‖))
    (hLσ : Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) (hv : v ∈ K) (hne : u ≠ v)
    (hdens : 4 * (d / σ) * Real.sqrt n
      ≤ densDist (Set.indicator K (fun x => f x * gaussianWeightReal (σ ^ 2) x)) u v) :
    2 * Real.sqrt 3 * d ≤ ‖u - v‖ := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := pow_pos hσ 2
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal (σ ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  -- positivity of `‖u − v‖` and of `R`
  have hpos : 0 < ‖u - v‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hne
  have hR0 : 0 < R := by
    have h1 := hKR u hu
    have h2 := hKR v hv
    have := norm_sub_le u v
    linarith
  -- the density is the plain product at `u` and `v`
  have hhu : Set.indicator K (fun x => f x * gaussianWeightReal (σ ^ 2) x) u
      = f u * gaussianWeightReal (σ ^ 2) u := Set.indicator_of_mem hu _
  have hhv : Set.indicator K (fun x => f x * gaussianWeightReal (σ ^ 2) x) v
      = f v * gaussianWeightReal (σ ^ 2) v := Set.indicator_of_mem hv _
  -- the two-sided multiplicative bound
  set s : ℝ := (Lf + R / σ ^ 2) * ‖u - v‖ with hsdef
  have hsplit : ∀ w z : EuclideanSpace ℝ (Fin n), w ∈ K → z ∈ K → ‖w - z‖ = ‖u - v‖ →
      f w * gaussianWeightReal (σ ^ 2) w
        ≤ f z * gaussianWeightReal (σ ^ 2) z * Real.exp s := by
    intro w z hw hz hwz
    have h1 : f w ≤ f z * Real.exp (Lf * ‖u - v‖) := by
      have := hfLip w hw z hz
      rwa [hwz] at this
    have h2 : gaussianWeightReal (σ ^ 2) w
        ≤ gaussianWeightReal (σ ^ 2) z * Real.exp (R / σ ^ 2 * ‖u - v‖) := by
      have := gaussianWeightReal_le_mul_exp (n := n) hσ (hKR w hw) (hKR z hz)
      rwa [hwz] at this
    have hmul : f w * gaussianWeightReal (σ ^ 2) w
        ≤ (f z * Real.exp (Lf * ‖u - v‖))
          * (gaussianWeightReal (σ ^ 2) z * Real.exp (R / σ ^ 2 * ‖u - v‖)) :=
      mul_le_mul h1 h2 (hgpos w).le
        (mul_nonneg (hfKpos z hz).le (Real.exp_pos _).le)
    have hrw : (f z * Real.exp (Lf * ‖u - v‖))
          * (gaussianWeightReal (σ ^ 2) z * Real.exp (R / σ ^ 2 * ‖u - v‖))
        = f z * gaussianWeightReal (σ ^ 2) z * Real.exp s := by
      rw [hsdef, add_mul, Real.exp_add]
      ring
    rwa [hrw] at hmul
  have hbound : densDist (Set.indicator K (fun x => f x * gaussianWeightReal (σ ^ 2) x)) u v
      ≤ s := by
    refine densDist_le_of_exp_bound ?_ ?_ ?_ ?_
    · rw [hhu]; exact mul_pos (hfKpos u hu) (hgpos u)
    · rw [hhv]; exact mul_pos (hfKpos v hv) (hgpos v)
    · rw [hhu, hhv]; exact hsplit u v hu hv rfl
    · rw [hhu, hhv]; exact hsplit v u hv hu (by rw [norm_sub_rev])
  -- combine
  have hstep : 4 * (d / σ) * Real.sqrt n ≤ (Lf + R / σ ^ 2) * ‖u - v‖ := le_trans hdens hbound
  have hscaled : 4 * σ * d * Real.sqrt n ≤ (σ ^ 2 * Lf + R) * ‖u - v‖ := by
    have h2 := mul_le_mul_of_nonneg_right hstep hσ2.le
    have hl : 4 * (d / σ) * Real.sqrt n * σ ^ 2 = 4 * σ * d * Real.sqrt n := by
      field_simp
    have hr : (Lf + R / σ ^ 2) * ‖u - v‖ * σ ^ 2 = (σ ^ 2 * Lf + R) * ‖u - v‖ := by
      field_simp
    rwa [hl, hr] at h2
  have hP : 0 < σ ^ 2 * Lf + R := by nlinarith
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [mul_lt_mul_of_pos_left hlt hP, mul_le_mul_of_nonneg_left hLσ (by linarith : (0:ℝ) ≤ 2 * d)]

end Separation

/-! ### (B), landed: disjoint open enlargements at any strictly smaller `d` -/

section Enlargement

variable {n : ℕ}

/-- **(B), landed, for the weighted density.**

Given the separation hypothesis at `d > 0` for `h = 1_K·f·e^{−‖x‖²/(2σ²)}` and
`√3·(σ²Lf + R) ≤ 2σ√n`, the `√3(d−d')`-thickenings of `S₁ ∩ K` and `S₂ ∩ K` are **disjoint
open** supersets of them on which the *metric* branch holds for **every** pair, at the threshold
`2√3·d'`.

Verbatim `Arlib.exists_disjoint_open_enlargement_gaussianIndicator` with the crux replaced by
`Arlib.norm_sub_ge_of_densDist_weighted`. -/
theorem exists_disjoint_open_enlargement_weighted {σ d d' R Lf : ℝ} (hσ : 0 < σ)
    (hd : 0 < d) (hd'0 : 0 < d') (hd'd : d' < d) (hLf : 0 ≤ Lf)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfKpos : ∀ x ∈ K, 0 < f x)
    (hfLip : ∀ u ∈ K, ∀ v ∈ K, f u ≤ f v * Real.exp (Lf * ‖u - v‖))
    (hLσ : Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n)
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin n))} (hdisj : Disjoint S₁ S₂)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      2 * Real.sqrt 3 * d ≤ ‖u - v‖ ∨
        4 * (d / σ) * Real.sqrt n
          ≤ densDist (Set.indicator K (fun x => f x * gaussianWeightReal (σ ^ 2) x)) u v) :
    ∃ U₁ U₂ : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧ S₁ ∩ K ⊆ U₁ ∧ S₂ ∩ K ⊆ U₂ ∧
        ∀ u ∈ U₁, ∀ v ∈ U₂, 2 * Real.sqrt 3 * d' ≤ ‖u - v‖ := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hAsep : ∀ u ∈ S₁ ∩ K, ∀ v ∈ S₂ ∩ K, 2 * Real.sqrt 3 * d ≤ ‖u - v‖ := by
    intro u hu v hv
    rcases hsep u hu.1 v hv.1 with hmetric | hdens
    · exact hmetric
    · refine norm_sub_ge_of_densDist_weighted hσ hd hLf hKR hfKpos hfLip hLσ hu.2 hv.2 ?_ hdens
      rintro rfl
      exact (Set.disjoint_left.mp hdisj hu.1) hv.1
  set ρ : ℝ := Real.sqrt 3 * (d - d') with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact mul_pos hs3 (by linarith)
  refine ⟨Metric.thickening ρ (S₁ ∩ K), Metric.thickening ρ (S₂ ∩ K),
    Metric.isOpen_thickening, Metric.isOpen_thickening, ?_,
    Metric.self_subset_thickening hρ _, Metric.self_subset_thickening hρ _, ?_⟩
  · rw [Set.disjoint_left]
    intro a ha hb
    have hcontr := norm_sub_ge_of_mem_thickening hAsep ha hb
    rw [sub_self, norm_zero] at hcontr
    have harith : 2 * Real.sqrt 3 * d - 2 * ρ = 2 * Real.sqrt 3 * d' := by
      rw [hρdef]; ring
    rw [harith] at hcontr
    have : 0 < 2 * Real.sqrt 3 * d' := by positivity
    linarith
  · intro u hu v hv
    have hcontr := norm_sub_ge_of_mem_thickening hAsep hu hv
    have harith : 2 * Real.sqrt 3 * d - 2 * ρ = 2 * Real.sqrt 3 * d' := by
      rw [hρdef]; ring
    rw [harith] at hcontr
    exact hcontr

end Enlargement

/-! ### (A): dominated convergence for the weighted continuous approximations -/

section Approximation

variable {n : ℕ}

/-- **A continuous, nonnegative, integrable function that is positive somewhere has positive
integral.** -/
theorem integral_pos_of_continuous_of_pos {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hgc : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : 0 < g x₀) : 0 < ∫ x, g x := by
  rw [integral_pos_iff_support_of_nonneg hg0 hgi]
  have hopen : IsOpen {x : EuclideanSpace ℝ (Fin n) | 0 < g x} :=
    isOpen_lt continuous_const hgc
  refine lt_of_lt_of_le (hopen.measure_pos volume ⟨x₀, hx₀⟩) (measure_mono ?_)
  intro z hz
  exact ne_of_gt hz

/-- **(A), landed, for the weighted density.**

`e^{−j·dist(x,C)}·f(x)·e^{−‖x‖²/(2σ²)} → 1_C(x)·f(x)·e^{−‖x‖²/(2σ²)}` in every set integral, by
dominated convergence with dominating function `f·e^{−‖x‖²/(2σ²)}` itself.  The only new
hypothesis over the indicator case is that this dominating function be integrable — the Gaussian
alone no longer dominates once an unbounded `f` is allowed. -/
theorem tendsto_setIntegral_expNegInfDist_mul_weighted {σ : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (hfi : Integrable fun x : EuclideanSpace ℝ (Fin n) => f x * gaussianWeightReal (σ ^ 2) x)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCcl : IsClosed C) (hCne : C.Nonempty)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    Tendsto (fun j : ℕ => ∫ x in S,
        Real.exp (-((j : ℝ) * Metric.infDist x C)) * f x * gaussianWeightReal (σ ^ 2) x)
      atTop (𝓝 (∫ x in S,
        Set.indicator C (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)) := by
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal (σ ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hcInf : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Metric.infDist x C) :=
    Metric.continuous_infDist_pt C
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => f x * gaussianWeightReal (σ ^ 2) x) (fun j => ?_) hfi.restrict (fun j => ?_) ?_
  · exact (((Real.continuous_exp.comp ((continuous_const.mul hcInf).neg)).mul hfc).mul
      (continuous_gaussianWeightReal _)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have hle : Real.exp (-((j : ℝ) * Metric.infDist x C)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg (Nat.cast_nonneg j) Metric.infDist_nonneg
    have h0 : 0 < Real.exp (-((j : ℝ) * Metric.infDist x C)) := Real.exp_pos _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg h0.le (hf0 x)) (hgpos x).le)]
    have h1 := mul_le_mul_of_nonneg_right hle (hf0 x)
    have h2 := mul_le_mul_of_nonneg_right h1 (hgpos x).le
    simpa using h2
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ C
    · have hz : Metric.infDist x C = 0 := Metric.infDist_zero_of_mem hx
      rw [Set.indicator_of_mem hx]
      simp only [hz, mul_zero, neg_zero, Real.exp_zero, one_mul]
      exact tendsto_const_nhds
    · have hz : 0 < Metric.infDist x C := (hCcl.notMem_iff_infDist_pos hCne).mp hx
      rw [Set.indicator_of_notMem hx]
      have hbot : Tendsto (fun j : ℕ => -((j : ℝ) * Metric.infDist x C)) atTop atBot := by
        have h1 : Tendsto (fun j : ℕ => (j : ℝ) * Metric.infDist x C) atTop atTop :=
          Filter.Tendsto.atTop_mul_const hz tendsto_natCast_atTop_atTop
        exact tendsto_neg_atTop_atBot.comp h1
      have h2 : Tendsto (fun j : ℕ => Real.exp (-((j : ℝ) * Metric.infDist x C))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hbot
      simpa using (h2.mul_const (f x)).mul_const (gaussianWeightReal (σ ^ 2) x)

end Approximation

/-! ### The deliverable -/

section Main

variable {n : ℕ}

/-- **`thm:iso` for the weighted density `1_K·f·e^{−‖x‖²/(2σ²)}`, with `S₁ S₂ S₃` merely
measurable.**

This is `Arlib.gaussianIndicator_isoperimetry_measurable_logTwo`
(`Arlib/Convexity/OneDimSharp.lean:676`) with the indicator density `1_K·e^{−‖x‖²/(2σ²)}`
replaced by `1_K·f·e^{−‖x‖²/(2σ²)}` for a log-concave cofactor `f`.  It is the same statement,
at the same sharp constant `d/σ`, with the same metric threshold `d / log 2`, over the same
merely-measurable partition.

**The hypothesis bundle on `f`, and why each piece is load-bearing.**

* `hf0`, `hflc`, `hfc`, `hfB` — nonnegative, log-concave, continuous and bounded.  These are
  what the open/closed capstone `Arlib.gaussianRestricted_isoperimetry_openClosed_logTwo` asks
  of the *approximating* densities `h_j = e^{−j·dist(x,K̄)}·f·e^{−‖x‖²/(2σ²)}`, whose log-concave
  factor is `e^{−j·dist(x,K̄)}·f`.  Continuity is needed **globally**, not merely on `K`: the
  approximant `e^{−j·dist(x,K̄)}` is strictly positive off `K` too, so it cannot mask a
  discontinuity of `f` there.
* `hfKpos`, `hfLip`, `hLf`, `hLσ` — **the new content**, and the point of the file.  Log-concavity,
  continuity and strict positivity on `K` are *not* enough.  The `(B)` step needs the density
  branch to have **quantitative** metric content on `K`, i.e. `d_h(u,v) ≤ M·‖u − v‖`; continuity
  gives only a modulus of continuity, which cannot reach the *fixed* thresholds `d / log 2` and
  `4(d/σ)√n` that the statement names.  So `f` must be log-Lipschitz on `K` with an explicit
  constant `Lf`, and `Lf` must be small enough relative to `σ`, `R` and `n`:
  `√3·(σ²Lf + R) ≤ 2σ√n`.  At `Lf = 0` this is `√3·R ≤ 2σ√n`, verbatim the indicator theorem's
  `hRσ` — so the generalisation is conservative.
* `hK0` is used only to know `K` is nonempty.

**Proof outline** — the indicator one, unchanged.  `h` vanishes off `K`, so intersecting
`S₁, S₂` with `K` changes no integral, and on `K` the density branch has metric content
(`Arlib.norm_sub_ge_of_densDist_weighted`).  At any `d' < d` this yields disjoint open
`U₁ ⊇ S₁ ∩ K`, `U₂ ⊇ S₂ ∩ K` on which the metric branch holds for **all** pairs
(`Arlib.exists_disjoint_open_enlargement_weighted`, invoked at the rescaled radius
`d/(2√3·log 2)`), so the open/closed capstone applies to `U₁, U₂, (U₁ ∪ U₂)ᶜ` with the metric
branch supplied unconditionally — `densDist h_j` never appears.  Let `j → ∞` (dominated
convergence, `Arlib.tendsto_setIntegral_expNegInfDist_mul_weighted`), then `d' ↑ d`. -/
theorem weightedIndicator_isoperimetry_measurable_logTwo (hn : 2 ≤ n) {σ d R B Lf : ℝ}
    (hσ : 0 < σ) (hLf : 0 ≤ Lf)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hK0 : volume K ≠ 0)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hflc : IsLogConcave f) (hfc : Continuous f) (hfB : ∀ x, f x ≤ B)
    (hfKpos : ∀ x ∈ K, 0 < f x)
    (hfLip : ∀ u ∈ K, ∀ v ∈ K, f u ≤ f v * Real.exp (Lf * ‖u - v‖))
    (hLσ : Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (_hS₁ : MeasurableSet S₁) (_hS₂ : MeasurableSet S₂) (_hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨
        4 * (d / σ) * Real.sqrt n
          ≤ densDist (Set.indicator K (fun x => f x * gaussianWeightReal (σ ^ 2) x)) u v) :
    d / σ * ((∫ x in S₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
      ≤ (∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₃, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := by
  classical
  have hσsq : (0 : ℝ) < σ ^ 2 := pow_pos hσ 2
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal (σ ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hg1 : ∀ x : EuclideanSpace ℝ (Fin n), gaussianWeightReal (σ ^ 2) x ≤ 1 :=
    fun x => gaussianWeightReal_le_one hσsq x
  have hgi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal (σ ^ 2) x) :=
    integrable_gaussianWeightReal hσ
  have hB0 : (0 : ℝ) ≤ B := le_trans (hf0 0) (hfB 0)
  have hfgc : Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      f x * gaussianWeightReal (σ ^ 2) x := hfc.mul (continuous_gaussianWeightReal _)
  have hfg0 : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ f x * gaussianWeightReal (σ ^ 2) x :=
    fun x => mul_nonneg (hf0 x) (hgpos x).le
  have hfgi : Integrable fun x : EuclideanSpace ℝ (Fin n) =>
      f x * gaussianWeightReal (σ ^ 2) x := by
    refine (hgi.const_mul B).mono' hfgc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfg0 x)]
    exact mul_le_mul_of_nonneg_right (hfB x) (hgpos x).le
  have hh0 : ∀ x, 0 ≤ Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x :=
    fun x => Set.indicator_nonneg (fun y _ => hfg0 y) x
  have hhi : Integrable (Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y)) :=
    hfgi.indicator hK
  have hm₁ : 0 ≤ ∫ x in S₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x :=
    integral_nonneg fun x => hh0 x
  have hm₂ : 0 ≤ ∫ x in S₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x :=
    integral_nonneg fun x => hh0 x
  have hm₃ : 0 ≤ ∫ x in S₃, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x :=
    integral_nonneg fun x => hh0 x
  have hM : 0 ≤ ∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x :=
    integral_nonneg fun x => hh0 x
  rcases le_or_gt d 0 with hdle | hd
  · have hds : d / σ ≤ 0 := by
      rw [div_le_iff₀ hσ]; linarith
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hds (mul_nonneg hm₁ hm₂))
      (mul_nonneg hM hm₃)
  -- from here `0 < d`
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hEq
    rw [hEq] at hK0
    exact hK0 measure_empty
  obtain ⟨z₀, hz₀K⟩ := hKne
  have hCne : (closure K).Nonempty := ⟨z₀, subset_closure hz₀K⟩
  have hCconv : Convex ℝ (closure K) := hKc.closure
  have hCbdd : Bornology.IsBounded (closure K) := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := R)).subset ?_
    refine (closure_minimal ?_ Metric.isClosed_closedBall)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hKR x hx
  have hCcomp : IsCompact (closure K) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hCbdd
  have hS₃eq : (S₁ ∪ S₂)ᶜ = S₃ := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      have hmem : x ∈ S₁ ∪ S₂ ∪ S₃ := by rw [hpart.union]; trivial
      rcases hmem with (h1 | h2) | h3
      · exact absurd (Or.inl h1) hx
      · exact absurd (Or.inr h2) hx
      · exact h3
    · intro x hx hmem
      rcases hmem with h1 | h2
      · exact (Set.disjoint_left.mp hpart.disjoint₁₃ h1) hx
      · exact (Set.disjoint_left.mp hpart.disjoint₂₃ h2) hx
  -- the main estimate, for every `d' ∈ (0, d)`
  have key : ∀ d' : ℝ, 0 < d' → d' < d →
      d' / σ * ((∫ x in S₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in S₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        ≤ (∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in S₃, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := by
    intro d' hd'0 hd'd
    -- the enlargement machinery is reused at the rescaled radius `d/c`, `c = 2√3·log 2`
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hc0 : (0 : ℝ) < 2 * Real.sqrt 3 * Real.log 2 := by positivity
    have hc1 : (1 : ℝ) ≤ 2 * Real.sqrt 3 * Real.log 2 := by
      have h3 : (1.7 : ℝ) < Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
      have hl : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hprod : (1.7 : ℝ) * 0.6931471803 ≤ Real.sqrt 3 * Real.log 2 :=
        mul_le_mul h3.le hl.le (by norm_num) (by linarith)
      nlinarith [hprod]
    have hrescale : ∀ e : ℝ, 2 * Real.sqrt 3 * (e / (2 * Real.sqrt 3 * Real.log 2))
        = e / Real.log 2 := by
      intro e; field_simp
    have hsep' : ∀ u ∈ S₁, ∀ v ∈ S₂,
        2 * Real.sqrt 3 * (d / (2 * Real.sqrt 3 * Real.log 2)) ≤ ‖u - v‖ ∨
          4 * (d / (2 * Real.sqrt 3 * Real.log 2) / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (fun x => f x * gaussianWeightReal (σ ^ 2) x)) u v := by
      intro u hu v hv
      rcases hsep u hu v hv with hmetric | hdens
      · exact Or.inl (by rw [hrescale d]; exact hmetric)
      · refine Or.inr (le_trans ?_ hdens)
        have hdd : d / (2 * Real.sqrt 3 * Real.log 2) ≤ d := by
          rw [div_le_iff₀ hc0]
          nlinarith [hd.le, hc1]
        have hn0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
        have hds : d / (2 * Real.sqrt 3 * Real.log 2) / σ ≤ d / σ :=
          div_le_div_of_nonneg_right hdd hσ.le
        nlinarith [hds, hn0]
    obtain ⟨U₁, U₂, hU₁, hU₂, hUdisj, hsub₁, hsub₂, hUsep0⟩ :=
      exists_disjoint_open_enlargement_weighted (σ := σ)
        (d := d / (2 * Real.sqrt 3 * Real.log 2))
        (d' := d' / (2 * Real.sqrt 3 * Real.log 2)) hσ (div_pos hd hc0) (div_pos hd'0 hc0)
        (by gcongr) hLf hKR hfKpos hfLip hLσ hpart.disjoint₁₂ hsep'
    have hUsep : ∀ u ∈ U₁, ∀ v ∈ U₂, d' / Real.log 2 ≤ ‖u - v‖ := by
      intro u hu v hv
      have h := hUsep0 u hu v hv
      rwa [hrescale d'] at h
    have hpart' : IsPartition3 Set.univ U₁ U₂ (U₁ ∪ U₂)ᶜ :=
      { union := Set.union_compl_self (U₁ ∪ U₂)
        disjoint₁₂ := hUdisj
        disjoint₁₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inl ha)
        disjoint₂₃ := Set.disjoint_left.mpr fun a ha hc => hc (Or.inr ha) }
    -- the capstone, applied to the continuous approximations on `U₁, U₂, (U₁ ∪ U₂)ᶜ`
    have hcap : ∀ j : ℕ,
        d' / σ * ((∫ x in U₁, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * f x * gaussianWeightReal (σ ^ 2) x)
            * ∫ x in U₂, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * f x * gaussianWeightReal (σ ^ 2) x)
          ≤ (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * f x * gaussianWeightReal (σ ^ 2) x)
            * ∫ x in (U₁ ∪ U₂)ᶜ, Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))
              * f x * gaussianWeightReal (σ ^ 2) x := by
      intro j
      have hcInf : Continuous
          (fun x : EuclideanSpace ℝ (Fin n) => Metric.infDist x (closure K)) :=
        Metric.continuous_infDist_pt _
      have hec : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K)))) :=
        Real.continuous_exp.comp ((continuous_const.mul hcInf).neg)
      have he1 : ∀ x : EuclideanSpace ℝ (Fin n),
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) ≤ 1 := by
        intro x
        rw [Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg (Nat.cast_nonneg j) Metric.infDist_nonneg
      have he0 : ∀ x : EuclideanSpace ℝ (Fin n),
          0 < Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) := fun x => Real.exp_pos _
      have hFlc : IsLogConcave (fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x) :=
        IsLogConcave.mul (isLogConcave_exp_neg_infDist hCconv hCcomp hCne (Nat.cast_nonneg j))
          hflc (fun x => (he0 x).le) hf0
      have hjc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
            * gaussianWeightReal (σ ^ 2) x) :=
        (hec.mul hfc).mul (continuous_gaussianWeightReal _)
      have hjle : ∀ x : EuclideanSpace ℝ (Fin n),
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
              * gaussianWeightReal (σ ^ 2) x
            ≤ f x * gaussianWeightReal (σ ^ 2) x := by
        intro x
        have h1 := mul_le_mul_of_nonneg_right (he1 x) (hf0 x)
        have h2 := mul_le_mul_of_nonneg_right h1 (hgpos x).le
        simpa using h2
      have hjB : ∀ x : EuclideanSpace ℝ (Fin n),
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
              * gaussianWeightReal (σ ^ 2) x ≤ B := by
        intro x
        refine le_trans (hjle x) ?_
        have := mul_le_mul_of_nonneg_right (hfB x) (hgpos x).le
        nlinarith [hg1 x, hB0, hgpos x]
      have hj0 : ∀ x : EuclideanSpace ℝ (Fin n),
          0 ≤ Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
            * gaussianWeightReal (σ ^ 2) x :=
        fun x => mul_nonneg (mul_nonneg (he0 x).le (hf0 x)) (hgpos x).le
      have hji : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
            * gaussianWeightReal (σ ^ 2) x) := by
        refine hfgi.mono' hjc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hj0 x)]
        exact hjle x
      have hjmass : 0 < ∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
          * gaussianWeightReal (σ ^ 2) x :=
        integral_pos_of_continuous_of_pos hjc hj0 hji
          (x₀ := z₀) (mul_pos (mul_pos (he0 z₀) (hfKpos z₀ hz₀K)) (hgpos z₀))
      exact gaussianRestricted_isoperimetry_openClosed_logTwo hn hσ
        (f := fun x => Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x)
        (h := fun x => Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
          * gaussianWeightReal (σ ^ 2) x)
        (B := B)
        (fun x => mul_nonneg (he0 x).le (hf0 x)) hFlc
        (fun x => rfl) hjc hjB hji hpart' hU₁ hU₂ (hU₁.union hU₂).isClosed_compl hjmass
        (fun u hu v hv => Or.inl (hUsep u hu v hv))
    -- pass to the limit `j → ∞`
    have hlim : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        Tendsto (fun j : ℕ => ∫ x in S,
            Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
              * gaussianWeightReal (σ ^ 2) x)
          atTop (𝓝 (∫ x in S,
            Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)) := by
      intro S
      have h := tendsto_setIntegral_expNegInfDist_mul_weighted (n := n) (σ := σ) hf0 hfc hfgi
        (C := closure K) isClosed_closure hCne S
      rwa [setIntegral_indicator_closure_eq hKc _ S] at h
    have hlimU : Tendsto (fun j : ℕ => ∫ x,
        Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
          * gaussianWeightReal (σ ^ 2) x)
        atTop (𝓝 (∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)) := by
      have h := hlim Set.univ
      simpa only [MeasureTheory.setIntegral_univ] using h
    have hLHS : Tendsto (fun j : ℕ => d' / σ *
        ((∫ x in U₁, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
            * gaussianWeightReal (σ ^ 2) x)
          * ∫ x in U₂, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
            * gaussianWeightReal (σ ^ 2) x)) atTop
        (𝓝 (d' / σ * ((∫ x in U₁,
              Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in U₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x))) :=
      ((hlim U₁).mul (hlim U₂)).const_mul (d' / σ)
    have hRHS : Tendsto (fun j : ℕ =>
        (∫ x, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
            * gaussianWeightReal (σ ^ 2) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ, Real.exp (-((j : ℝ) * Metric.infDist x (closure K))) * f x
            * gaussianWeightReal (σ ^ 2) x) atTop
        (𝓝 ((∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ,
              Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)) :=
      hlimU.mul (hlim _)
    have hUineq : d' / σ * ((∫ x in U₁,
            Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in U₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        ≤ (∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ,
              Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x :=
      le_of_tendsto_of_tendsto' hLHS hRHS hcap
    -- monotonicity back to `S₁, S₂, S₃`
    have hcut : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
        (∫ x in S, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          = ∫ x in S ∩ K, f x * gaussianWeightReal (σ ^ 2) x := fun S => setIntegral_indicator hK
    have hmono : ∀ {S T : Set (EuclideanSpace ℝ (Fin n))}, S ⊆ T →
        (∫ x in S, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          ≤ ∫ x in T, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := by
      intro S T hST
      exact setIntegral_mono_set hhi.integrableOn
        (Filter.Eventually.of_forall hh0) hST.eventuallyLE
    have hcore₁ : (∫ x in S₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        = ∫ x in S₁ ∩ K, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := by
      rw [hcut S₁, hcut (S₁ ∩ K), Set.inter_assoc, Set.inter_self]
    have hcore₂ : (∫ x in S₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        = ∫ x in S₂ ∩ K, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := by
      rw [hcut S₂, hcut (S₂ ∩ K), Set.inter_assoc, Set.inter_self]
    have hsetiii : ((S₁ ∩ K) ∪ (S₂ ∩ K))ᶜ ∩ K = S₃ ∩ K := by
      ext x
      constructor
      · rintro ⟨hnot, hxK⟩
        refine ⟨?_, hxK⟩
        rw [← hS₃eq]
        intro hmem
        rcases hmem with h1 | h2
        · exact hnot (Or.inl ⟨h1, hxK⟩)
        · exact hnot (Or.inr ⟨h2, hxK⟩)
      · rintro ⟨h3, hxK⟩
        refine ⟨?_, hxK⟩
        rintro (⟨h1, -⟩ | ⟨h2, -⟩)
        · exact (Set.disjoint_left.mp hpart.disjoint₁₃ h1) h3
        · exact (Set.disjoint_left.mp hpart.disjoint₂₃ h2) h3
    have hcore₃ : (∫ x in ((S₁ ∩ K) ∪ (S₂ ∩ K))ᶜ,
          Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        = ∫ x in S₃, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := by
      rw [hcut _, hcut S₃, hsetiii]
    have hU₃sub : (U₁ ∪ U₂)ᶜ ⊆ ((S₁ ∩ K) ∪ (S₂ ∩ K))ᶜ := by
      refine Set.compl_subset_compl.mpr ?_
      exact Set.union_subset_union hsub₁ hsub₂
    have hle₁ : (∫ x in S₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        ≤ ∫ x in U₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := by
      rw [hcore₁]; exact hmono hsub₁
    have hle₂ : (∫ x in S₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        ≤ ∫ x in U₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := by
      rw [hcore₂]; exact hmono hsub₂
    have hle₃ : (∫ x in (U₁ ∪ U₂)ᶜ,
          Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        ≤ ∫ x in S₃, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := by
      rw [← hcore₃]; exact hmono hU₃sub
    have hd'σ : 0 ≤ d' / σ := (div_pos hd'0 hσ).le
    calc d' / σ * ((∫ x in S₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in S₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        ≤ d' / σ * ((∫ x in U₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in U₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hle₁ hle₂ hm₂ (le_trans hm₁ hle₁)) hd'σ
      _ ≤ (∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in (U₁ ∪ U₂)ᶜ,
              Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x := hUineq
      _ ≤ (∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
          * ∫ x in S₃, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x :=
          mul_le_mul_of_nonneg_left hle₃ hM
  -- let `d' ↑ d`
  by_contra hcon
  rw [not_le] at hcon
  set P : ℝ := (∫ x in S₁, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
    * ∫ x in S₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x with hPdef
  set Q : ℝ := (∫ x, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
    * ∫ x in S₃, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x with hQdef
  have hQ0 : 0 ≤ Q := mul_nonneg hM hm₃
  have hPnn : 0 ≤ P := mul_nonneg hm₁ hm₂
  have hP : 0 < P := by
    rcases hPnn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, mul_zero] at hcon
      linarith
  have hcd : σ * Q / P < d := by
    rw [div_lt_iff₀ hP]
    have hstep : Q * σ < d / σ * P * σ := mul_lt_mul_of_pos_right hcon hσ
    have hrw : d / σ * P * σ = d * P := by field_simp
    rw [hrw] at hstep
    linarith
  set d' : ℝ := (max (σ * Q / P) (d / 2) + d) / 2 with hd'def
  have hmaxlt : max (σ * Q / P) (d / 2) < d := max_lt hcd (by linarith)
  have hd'lt : d' < d := by rw [hd'def]; linarith
  have hd'gt : max (σ * Q / P) (d / 2) < d' := by rw [hd'def]; linarith
  have hhalf : d / 2 < d' := lt_of_le_of_lt (le_max_right _ _) hd'gt
  have hd'pos : 0 < d' := by linarith
  have hcc : σ * Q / P < d' := lt_of_le_of_lt (le_max_left _ _) hd'gt
  rw [div_lt_iff₀ hP] at hcc
  have hkey := key d' hd'pos hd'lt
  have hstep2 : d' / σ * P * σ ≤ Q * σ := mul_le_mul_of_nonneg_right hkey hσ.le
  have hrw2 : d' / σ * P * σ = d' * P := by field_simp
  rw [hrw2] at hstep2
  linarith

end Main

/-! ### The instantiation at `f := ℓ` -/

section Ell

variable {n : ℕ}

/-- **`thm:iso` for the `ℓ`-weighted Gaussian density `1_K·ℓ·e^{−‖x‖²/(2σ²)}`, with
`S₁ S₂ S₃` merely measurable.**

`Arlib.weightedIndicator_isoperimetry_measurable_logTwo` with `f` pinned to the local
conductance.  `hf0` is `ENNReal.toReal_nonneg`, `hflc` is `Arlib.isLogConcave_ell_toReal`,
`hfc` is `Arlib.continuous_ell_toReal`, and `hfB` is `Arlib.MarkovChains.ell_le_one` at `B = 1`.

The two binders that are **not** discharged here are the new ones: `hellKpos` (strict positivity
of `ℓ` on `K`) and `hellLip` (`ℓ` log-Lipschitz on `K` with constant `Lf`), together with the
compatibility `hLσ`.  They are genuinely extra content about `ℓ`, not isoperimetry, and this
file does not prove them for a general convex body — `Arlib.ellGaussian_isoperimetry_measurable_logTwo_strict_witness`
exhibits a body on which they hold with `Lf = 0`, so the statement is not vacuous.

**Scope.**  This is an isoperimetric inequality and nothing else.  It is not a conductance
bound, not a mixing bound, and not a runtime claim.  It is also **not** by itself the `hiso`
binder of `Arlib.MarkovChains.conductance_speedyWalk_ge_of_convex`: that binder is for the
density of a measure the *speedy walk* is reversible for, and the only such measures in this
repository are the scalar multiples of `Arlib.MarkovChains.ellMeasure K δ`, whose density is
`1_K·ℓ` with **no** Gaussian factor.  See the module docstring for what a kernel reversible for
`1_K·ℓ·γ` would have to be. -/
theorem ellGaussian_isoperimetry_measurable_logTwo (hn : 2 ≤ n) {σ d δ R Lf : ℝ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hLf : 0 ≤ Lf)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hK0 : volume K ≠ 0)
    (hellKpos : ∀ x ∈ K, 0 < (ell K δ x).toReal)
    (hellLip : ∀ u ∈ K, ∀ v ∈ K,
      (ell K δ u).toReal ≤ (ell K δ v).toReal * Real.exp (Lf * ‖u - v‖))
    (hLσ : Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n)
    {S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))}
    (hpart : IsPartition3 Set.univ S₁ S₂ S₃)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) (hS₃ : MeasurableSet S₃)
    (hsep : ∀ u ∈ S₁, ∀ v ∈ S₂,
      d / Real.log 2 ≤ ‖u - v‖ ∨
        4 * (d / σ) * Real.sqrt n
          ≤ densDist (Set.indicator K
              (fun x => (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x)) u v) :
    d / σ * ((∫ x in S₁,
          Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₂,
          Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
      ≤ (∫ x, Set.indicator K
            (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₃,
          Set.indicator K (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x := by
  have hn0 : n ≠ 0 := by omega
  have hell1 : ∀ x : EuclideanSpace ℝ (Fin n), (ell K δ x).toReal ≤ 1 := by
    intro x
    have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K δ x)
    simpa using this
  exact weightedIndicator_isoperimetry_measurable_logTwo (B := 1) hn hσ hLf hK hKc hKR hK0
    (fun _ => ENNReal.toReal_nonneg) (isLogConcave_ell_toReal hK hKc δ)
    (continuous_ell_toReal hn0 hδ) hell1 hellKpos hellLip hLσ hpart hS₁ hS₂ hS₃ hsep

end Ell

/-! ### Non-vacuity -/

section Witness

variable {n : ℕ}

/-- **The slab geometry of the non-vacuity witnesses.**

For a unit vector `e` and a nonnegative integrable `g` bounded below by `c > 0` on the closed
ball of radius `1/2`, both open half-spaces `⟪e,x⟫ < −1/8` and `1/8 < ⟪e,x⟫` carry strictly
positive `g`-mass: the balls of radius `1/16` about `∓(1/4)·e` sit inside them and inside the
half-radius ball.  Shared by the two witnesses below. -/
theorem slab_setIntegral_pos {g : EuclideanSpace ℝ (Fin n) → ℝ} (hgi : Integrable g)
    (hg0 : ∀ x, 0 ≤ g x) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 → c ≤ g x)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) :
    (0 < ∫ x in {x : EuclideanSpace ℝ (Fin n) | (inner ℝ e x : ℝ) < -(1 / 8 : ℝ)}, g x) ∧
      0 < ∫ x in {x : EuclideanSpace ℝ (Fin n) | (1 / 8 : ℝ) < (inner ℝ e x : ℝ)}, g x := by
  have hballs : ∀ r : ℝ, |r| ≤ 1 / 4 → ∀ x ∈ Metric.ball (r • e) (1 / 16),
      ‖x‖ ≤ 1 / 2 ∧ |(inner ℝ e x : ℝ) - r| < 1 / 16 := by
    intro r hr x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hre : ‖r • e‖ ≤ 1 / 4 := by
      rw [norm_smul, Real.norm_eq_abs, he, mul_one]; exact hr
    refine ⟨?_, ?_⟩
    · have hle : ‖x‖ ≤ ‖x - r • e‖ + ‖r • e‖ := by
        simpa using norm_add_le (x - r • e) (r • e)
      linarith
    · have hip := abs_real_inner_le_norm e (x - r • e)
      rw [he, one_mul, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, he] at hip
      simpa using hip.trans_lt hx
  constructor
  · refine setIntegral_pos_of_ball_le (z := (-(1 / 4 : ℝ) • e)) (r := 1 / 16) (c := c)
      hgi hg0 (by norm_num) hc ?_ ?_
    · intro x hx
      obtain ⟨-, hx2⟩ := hballs (-(1 / 4)) (by rw [abs_le]; norm_num) x hx
      simp only [Set.mem_setOf_eq]
      rw [abs_lt] at hx2
      linarith [hx2.2]
    · intro x hx
      exact hlow x (hballs (-(1 / 4)) (by rw [abs_le]; norm_num) x hx).1
  · refine setIntegral_pos_of_ball_le (z := ((1 / 4 : ℝ) • e)) (r := 1 / 16) (c := c)
      hgi hg0 (by norm_num) hc ?_ ?_
    · intro x hx
      obtain ⟨-, hx2⟩ := hballs (1 / 4) (by rw [abs_le]; norm_num) x hx
      simp only [Set.mem_setOf_eq]
      rw [abs_lt] at hx2
      linarith [hx2.1]
    · intro x hx
      exact hlow x (hballs (1 / 4) (by rw [abs_le]; norm_num) x hx).1

/-- `(1/32)/log 2 ≤ 1/4`, the arithmetic behind the metric branch of both witnesses. -/
theorem thirtysecond_div_logTwo_le : (1 / 32 : ℝ) / Real.log 2 ≤ 1 / 4 := by
  have hl : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl0 : (0 : ℝ) < Real.log 2 := by linarith
  rw [div_le_iff₀ hl0]
  linarith

/-- **Strict non-vacuity for `Arlib.weightedIndicator_isoperimetry_measurable_logTwo`.**

Every hypothesis is met outright — not vacuously — at data whose left-hand side is *strictly
positive*, so the conclusion is not the trivial `0 ≤ something`:

  `K = closedBall 0 (1/2)`, `σ = 1`, `R = 1/2`, `d = 1/32`, `B = 1`,
  `f(x) = e^{−‖x‖/2}` (log-concave, continuous, `≤ 1`, positive, log-Lipschitz with `Lf = 1/2`),
  `S₁ = {⟪e,x⟫ < −1/8}`, `S₂ = {1/8 < ⟪e,x⟫}`, `S₃` the closed slab between them.

`f` is **not** constant, so this is a genuine test of the weighted theorem and not the indicator
one in disguise.  `hLσ` reads `√3·(1/2 + 1/2) = √3 ≤ 2√n`, true since `√3 ≤ 2 ≤ 2√n` for
`n ≥ 2`; the separation fires on the *metric* branch, `(1/32)/log 2 ≤ 1/4 ≤ ‖u − v‖`.  The two
masses are positive because balls of radius `1/16` about `∓(1/4)e` lie inside `K ∩ S₁` and
`K ∩ S₂`, where the density is at least `e^{−1/4}·e^{−1/2}`. -/
theorem weightedIndicator_isoperimetry_measurable_logTwo_strict_witness (hn : 2 ≤ n) :
    ∃ (K S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d R B Lf : ℝ)
      (f : EuclideanSpace ℝ (Fin n) → ℝ),
      0 < σ ∧ 0 < d ∧ 0 ≤ Lf ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ volume K ≠ 0 ∧
      (∀ x, 0 ≤ f x) ∧ IsLogConcave f ∧ Continuous f ∧ (∀ x, f x ≤ B) ∧
      (∀ x ∈ K, 0 < f x) ∧
      (∀ u ∈ K, ∀ v ∈ K, f u ≤ f v * Real.exp (Lf * ‖u - v‖)) ∧
      (∃ x ∈ K, ∃ y ∈ K, f x ≠ f y) ∧
      Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        d / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (d / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (fun x => f x * gaussianWeightReal (σ ^ 2) x)) u v) ∧
      (S₁ ∩ K).Nonempty ∧ (S₂ ∩ K).Nonempty ∧
      0 < d / σ * ((∫ x in S₁,
            Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₂, Set.indicator K (fun y => f y * gaussianWeightReal (σ ^ 2) y) x) := by
  classical
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  have hee : (inner ℝ e e : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  set K : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 (1 / 2) with hKdef
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (-(1 / 2 * ‖x‖)) with hfdef
  have hKmem : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 → x ∈ K := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right]
    exact hx
  have hKmeas : MeasurableSet K := measurableSet_closedBall
  have hKconv : Convex ℝ K := convex_closedBall _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (1 / 2 : ℝ) := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hK0 : volume K ≠ 0 := by
    have : 0 < volume K :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by norm_num : (0:ℝ) < 1/2))
        (measure_mono Metric.ball_subset_closedBall)
    exact this.ne'
  -- the cofactor
  have hf0 : ∀ x, 0 ≤ f x := fun x => (Real.exp_pos _).le
  have hfpos : ∀ x, 0 < f x := fun x => Real.exp_pos _
  have hfc : Continuous f := by
    rw [hfdef]
    exact Real.continuous_exp.comp ((continuous_const.mul continuous_norm).neg)
  have hflc : IsLogConcave f := by
    have hconv : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
        (fun x => (1 / 2 : ℝ) * ‖x‖) := by
      simpa only [smul_eq_mul] using convexOn_univ_norm.smul (by norm_num : (0:ℝ) ≤ 1 / 2)
    exact isLogConcave_exp hconv.neg
  have hfB : ∀ x, f x ≤ 1 := by
    intro x
    rw [hfdef, Real.exp_le_one_iff, neg_nonpos]
    positivity
  have hfLip : ∀ u ∈ K, ∀ v ∈ K, f u ≤ f v * Real.exp ((1 / 2 : ℝ) * ‖u - v‖) := by
    intro u _ v _
    rw [hfdef]
    simp only
    rw [← Real.exp_add, Real.exp_le_exp]
    have hd : ‖v‖ - ‖u‖ ≤ ‖u - v‖ :=
      le_trans (by linarith [neg_abs_le (‖u‖ - ‖v‖)]) (abs_norm_sub_norm_le u v)
    linarith
  -- the density
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal ((1:ℝ) ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hgi : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal ((1:ℝ) ^ 2) x) :=
    integrable_gaussianWeightReal one_pos
  have hfgi : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => f x * gaussianWeightReal ((1:ℝ) ^ 2) x) := by
    refine hgi.mono' ((hfc.mul (continuous_gaussianWeightReal _)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (hgpos x).le)]
    exact mul_le_of_le_one_left (hgpos x).le (hfB x)
  have hhi : Integrable
      (Set.indicator K (fun y => f y * gaussianWeightReal ((1:ℝ) ^ 2) y)) :=
    hfgi.indicator hKmeas
  have hh0 : ∀ x, 0 ≤ Set.indicator K (fun y => f y * gaussianWeightReal ((1:ℝ) ^ 2) y) x :=
    fun x => Set.indicator_nonneg (fun y _ => mul_nonneg (hf0 y) (hgpos y).le) x
  have hlow : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 →
      Real.exp (-(1:ℝ) / 4) * Real.exp (-(1:ℝ) / 2)
        ≤ Set.indicator K (fun y => f y * gaussianWeightReal ((1:ℝ) ^ 2) y) x := by
    intro x hx
    rw [Set.indicator_of_mem (hKmem x hx) _]
    have h1 : Real.exp (-(1:ℝ) / 4) ≤ f x := by
      rw [hfdef]
      refine Real.exp_le_exp.mpr ?_
      linarith
    have h2 : Real.exp (-(1:ℝ) / 2) ≤ gaussianWeightReal ((1:ℝ) ^ 2) x := by
      rw [gaussianWeightReal]
      refine Real.exp_le_exp.mpr ?_
      have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
      have h2' : (2:ℝ) * (1:ℝ) ^ 2 = 2 := by norm_num
      rw [h2']
      linarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (hf0 x)
  obtain ⟨hp1, hp2⟩ := slab_setIntegral_pos hhi hh0
    (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hlow he
  -- the two core points
  have hmec : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) :=
    continuous_const.inner continuous_id
  have hS1meas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) | (inner ℝ e x : ℝ) < -(1 / 8 : ℝ)} :=
    (isOpen_lt hmec continuous_const).measurableSet
  have hS2meas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) | (1 / 8 : ℝ) < (inner ℝ e x : ℝ)} :=
    (isOpen_lt continuous_const hmec).measurableSet
  have hS3meas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) |
        -(1 / 8 : ℝ) ≤ (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) ≤ 1 / 8} :=
    ((isClosed_le continuous_const hmec).inter (isClosed_le hmec continuous_const)).measurableSet
  have hnrmp : ‖(-(1 / 4 : ℝ)) • e‖ = 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]
  have hnrmq : ‖((1 / 4 : ℝ)) • e‖ = 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]
  refine ⟨K, {x | (inner ℝ e x : ℝ) < -(1 / 8 : ℝ)}, {x | (1 / 8 : ℝ) < (inner ℝ e x : ℝ)},
    {x | -(1 / 8 : ℝ) ≤ (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) ≤ 1 / 8},
    1, 1 / 32, 1 / 2, 1, 1 / 2, f,
    one_pos, by norm_num, by norm_num, hKmeas, hKconv, hKR, hK0,
    hf0, hflc, hfc, hfB, fun x _ => hfpos x, hfLip, ?_, ?_,
    isPartition3_slab e (by norm_num : (0:ℝ) ≤ 1 / 8),
    hS1meas, hS2meas, hS3meas,
    ?_, ?_, ?_, ?_⟩
  · -- `f` is not constant on `K`
    refine ⟨0, hKmem 0 (by simp), (1 / 4 : ℝ) • e, hKmem _ (by rw [hnrmq]; norm_num), ?_⟩
    rw [hfdef]
    simp only [norm_zero, mul_zero, neg_zero, Real.exp_zero, hnrmq]
    intro hcon
    have := Real.exp_lt_one_iff.2 (by norm_num : -((1:ℝ) / 2 * (1 / 4)) < 0)
    rw [← hcon] at this
    exact absurd this (lt_irrefl 1)
  · -- `hLσ`
    have hs3 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have hsn : (1 : ℝ) ≤ Real.sqrt n := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h1
    nlinarith
  · -- the separation hypothesis, metric branch
    intro u hu v hv
    left
    have hgeo := two_mul_le_norm_sub_of_inner_lt (e := e) he (c := (1 / 8 : ℝ)) hu hv
    have := thirtysecond_div_logTwo_le
    linarith
  · exact ⟨(-(1 / 4 : ℝ)) • e, by
      simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]; norm_num,
      hKmem _ (by rw [hnrmp]; norm_num)⟩
  · exact ⟨((1 / 4 : ℝ)) • e, by
      simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]; norm_num,
      hKmem _ (by rw [hnrmq]; norm_num)⟩
  · have h1 : (0:ℝ) < (1 / 32 : ℝ) / 1 := by norm_num
    exact mul_pos h1 (mul_pos hp1 hp2)

/-- **Strict non-vacuity for `Arlib.ellGaussian_isoperimetry_measurable_logTwo`.**

The two binders that instantiation does not discharge — `ℓ` strictly positive on `K` and `ℓ`
log-Lipschitz on `K` — are met **with `Lf = 0`** on a body where `ℓ` is *constant*:

  `K = closedBall 0 (1/2)`, `δ = 4`, `σ = 1`, `R = 1/2`, `d = 1/32`.

Since `‖z‖, ‖x‖ ≤ 1/2` gives `dist z x ≤ 1 < 4`, the whole body lies in every proposal ball
centred in it, so `B(x,4) ∩ K = K` and `ℓ(x) = vol K / vol(4Bₙ)` for every `x ∈ K` — a positive
constant.  `hLσ` therefore reduces to the indicator theorem's `√3·R ≤ 2σ√n`, i.e. `√3/2 ≤ 2√n`.
The separation fires on the metric branch and the left-hand side is strictly positive, so the
conclusion is not `0 ≤ something`. -/
theorem ellGaussian_isoperimetry_measurable_logTwo_strict_witness (hn : 2 ≤ n) :
    ∃ (K S₁ S₂ S₃ : Set (EuclideanSpace ℝ (Fin n))) (σ d δ R Lf : ℝ),
      0 < σ ∧ 0 < d ∧ 0 ≤ δ ∧ 0 ≤ Lf ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ volume K ≠ 0 ∧
      (∀ x ∈ K, 0 < (ell K δ x).toReal) ∧
      (∀ u ∈ K, ∀ v ∈ K,
        (ell K δ u).toReal ≤ (ell K δ v).toReal * Real.exp (Lf * ‖u - v‖)) ∧
      Real.sqrt 3 * (σ ^ 2 * Lf + R) ≤ 2 * σ * Real.sqrt n ∧
      IsPartition3 Set.univ S₁ S₂ S₃ ∧
      MeasurableSet S₁ ∧ MeasurableSet S₂ ∧ MeasurableSet S₃ ∧
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        d / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (d / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K
                (fun x => (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x)) u v) ∧
      (S₁ ∩ K).Nonempty ∧ (S₂ ∩ K).Nonempty ∧
      0 < d / σ * ((∫ x in S₁, Set.indicator K
              (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x)
        * ∫ x in S₂, Set.indicator K
              (fun y => (ell K δ y).toReal * gaussianWeightReal (σ ^ 2) y) x) := by
  classical
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, PiLp.norm_single]; norm_num
  have hee : (inner ℝ e e : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  set K : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 (1 / 2) with hKdef
  have hKmem : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 → x ∈ K := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right]
    exact hx
  have hKmeas : MeasurableSet K := measurableSet_closedBall
  have hKconv : Convex ℝ K := convex_closedBall _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (1 / 2 : ℝ) := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hK0 : volume K ≠ 0 := by
    have : 0 < volume K :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by norm_num : (0:ℝ) < 1/2))
        (measure_mono Metric.ball_subset_closedBall)
    exact this.ne'
  have hKtop : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  -- the whole body sits inside every proposal ball centred in it
  have hsub : ∀ x ∈ K, K ⊆ Metric.ball x (4 : ℝ) := by
    intro x hx z hz
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 := hKR x hx
    have h2 := hKR z hz
    have := norm_sub_le z x
    linarith
  -- so `ℓ` is the constant `vol K / vol(4Bₙ)` on `K`
  have hellval : ∀ x ∈ K, ell K (4 : ℝ) x
      = volume K / volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 4) := by
    intro x hx
    rw [ell_apply, Set.inter_eq_self_of_subset_right (hsub x hx), volume_ball_eq]
  have hellpos : ∀ x ∈ K, 0 < (ell K (4:ℝ) x).toReal := by
    intro x hx
    refine ENNReal.toReal_pos ?_
      (ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K (4:ℝ) x))
    rw [hellval x hx]
    exact ENNReal.div_ne_zero.2 ⟨hK0, measure_ball_lt_top.ne⟩
  have hellLip : ∀ u ∈ K, ∀ v ∈ K,
      (ell K (4:ℝ) u).toReal ≤ (ell K (4:ℝ) v).toReal * Real.exp ((0:ℝ) * ‖u - v‖) := by
    intro u hu v hv
    rw [hellval u hu, hellval v hv, zero_mul, Real.exp_zero, mul_one]
  -- the density
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussianWeightReal ((1:ℝ) ^ 2) x :=
    fun x => gaussianWeightReal_pos _ x
  have hgi : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => gaussianWeightReal ((1:ℝ) ^ 2) x) :=
    integrable_gaussianWeightReal one_pos
  have hell1 : ∀ x : EuclideanSpace ℝ (Fin n), (ell K (4:ℝ) x).toReal ≤ 1 := by
    intro x
    have := ENNReal.toReal_mono ENNReal.one_ne_top (ell_le_one K (4:ℝ) x)
    simpa using this
  have hellc : Continuous fun x : EuclideanSpace ℝ (Fin n) => (ell K (4:ℝ) x).toReal :=
    continuous_ell_toReal (by omega) (by norm_num)
  have hfgi : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (ell K (4:ℝ) x).toReal * gaussianWeightReal ((1:ℝ) ^ 2) x) := by
    refine hgi.mono' ((hellc.mul (continuous_gaussianWeightReal _)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hgpos x).le)]
    exact mul_le_of_le_one_left (hgpos x).le (hell1 x)
  have hhi : Integrable (Set.indicator K
      (fun y => (ell K (4:ℝ) y).toReal * gaussianWeightReal ((1:ℝ) ^ 2) y)) :=
    hfgi.indicator hKmeas
  have hh0 : ∀ x, 0 ≤ Set.indicator K
      (fun y => (ell K (4:ℝ) y).toReal * gaussianWeightReal ((1:ℝ) ^ 2) y) x :=
    fun x => Set.indicator_nonneg
      (fun y _ => mul_nonneg ENNReal.toReal_nonneg (hgpos y).le) x
  -- the constant lower bound on the half-radius ball
  set c₀ : ℝ := (ell K (4:ℝ) 0).toReal with hc₀def
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hKmem 0 (by simp)
  have hc₀ : 0 < c₀ := hellpos 0 h0K
  have hlow : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 →
      c₀ * Real.exp (-(1:ℝ) / 2)
        ≤ Set.indicator K
            (fun y => (ell K (4:ℝ) y).toReal * gaussianWeightReal ((1:ℝ) ^ 2) y) x := by
    intro x hx
    have hxK : x ∈ K := hKmem x hx
    rw [Set.indicator_of_mem hxK _]
    have h1 : (ell K (4:ℝ) x).toReal = c₀ := by
      rw [hc₀def, hellval x hxK, hellval 0 h0K]
    have h2 : Real.exp (-(1:ℝ) / 2) ≤ gaussianWeightReal ((1:ℝ) ^ 2) x := by
      rw [gaussianWeightReal]
      refine Real.exp_le_exp.mpr ?_
      have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
      have h2' : (2:ℝ) * (1:ℝ) ^ 2 = 2 := by norm_num
      rw [h2']
      linarith
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 hc₀.le
  obtain ⟨hp1, hp2⟩ := slab_setIntegral_pos hhi hh0
    (mul_pos hc₀ (Real.exp_pos _)) hlow he
  have hmec : Continuous fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ e x : ℝ) :=
    continuous_const.inner continuous_id
  have hS1meas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) | (inner ℝ e x : ℝ) < -(1 / 8 : ℝ)} :=
    (isOpen_lt hmec continuous_const).measurableSet
  have hS2meas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) | (1 / 8 : ℝ) < (inner ℝ e x : ℝ)} :=
    (isOpen_lt continuous_const hmec).measurableSet
  have hS3meas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) |
        -(1 / 8 : ℝ) ≤ (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) ≤ 1 / 8} :=
    ((isClosed_le continuous_const hmec).inter (isClosed_le hmec continuous_const)).measurableSet
  have hnrmp : ‖(-(1 / 4 : ℝ)) • e‖ = 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]
  have hnrmq : ‖((1 / 4 : ℝ)) • e‖ = 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]
  refine ⟨K, {x | (inner ℝ e x : ℝ) < -(1 / 8 : ℝ)}, {x | (1 / 8 : ℝ) < (inner ℝ e x : ℝ)},
    {x | -(1 / 8 : ℝ) ≤ (inner ℝ e x : ℝ) ∧ (inner ℝ e x : ℝ) ≤ 1 / 8},
    1, 1 / 32, 4, 1 / 2, 0,
    one_pos, by norm_num, by norm_num, le_rfl, hKmeas, hKconv, hKR, hK0,
    hellpos, hellLip, ?_,
    isPartition3_slab e (by norm_num : (0:ℝ) ≤ 1 / 8),
    hS1meas, hS2meas, hS3meas,
    ?_, ?_, ?_, ?_⟩
  · -- `hLσ` at `Lf = 0`: `√3·(1/2) ≤ 2√n`
    have hs3 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
    have hsn : (1 : ℝ) ≤ Real.sqrt n := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h1
    nlinarith
  · intro u hu v hv
    left
    have hgeo := two_mul_le_norm_sub_of_inner_lt (e := e) he (c := (1 / 8 : ℝ)) hu hv
    have := thirtysecond_div_logTwo_le
    linarith
  · exact ⟨(-(1 / 4 : ℝ)) • e, by
      simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]; norm_num,
      hKmem _ (by rw [hnrmp]; norm_num)⟩
  · exact ⟨((1 / 4 : ℝ)) • e, by
      simp only [Set.mem_setOf_eq, real_inner_smul_right, hee, mul_one]; norm_num,
      hKmem _ (by rw [hnrmq]; norm_num)⟩
  · have h1 : (0:ℝ) < (1 / 32 : ℝ) / 1 := by norm_num
    exact mul_pos h1 (mul_pos hp1 hp2)

end Witness

end Arlib

/-! ### Axiom audit -/

#print axioms Arlib.densDist_le_of_exp_bound_of_le
#print axioms Arlib.densDist_le_of_exp_bound
#print axioms Arlib.gaussianWeightReal_le_mul_exp
#print axioms Arlib.norm_sub_ge_of_densDist_weighted
#print axioms Arlib.exists_disjoint_open_enlargement_weighted
#print axioms Arlib.integral_pos_of_continuous_of_pos
#print axioms Arlib.tendsto_setIntegral_expNegInfDist_mul_weighted
#print axioms Arlib.weightedIndicator_isoperimetry_measurable_logTwo
#print axioms Arlib.ellGaussian_isoperimetry_measurable_logTwo
#print axioms Arlib.slab_setIntegral_pos
#print axioms Arlib.thirtysecond_div_logTwo_le
#print axioms Arlib.weightedIndicator_isoperimetry_measurable_logTwo_strict_witness
#print axioms Arlib.ellGaussian_isoperimetry_measurable_logTwo_strict_witness
